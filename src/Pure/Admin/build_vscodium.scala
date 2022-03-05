/*  Title:      Pure/Admin/build_vscodium.scala
    Author:     Makarius

Build component for VSCodium (cross-compiled from sources for all platforms).
*/

package isabelle


import java.security.MessageDigest
import java.util.Base64


object Build_VSCodium
{
  /* global parameters */

  lazy val version: String = Isabelle_System.getenv_strict("ISABELLE_VSCODE_VERSION")
  val vscodium_repository = "https://github.com/VSCodium/vscodium.git"
  val vscodium_download = "https://github.com/VSCodium/vscodium/releases/download"

  def vscodium_exe(dir: Path): Path = dir + Path.explode("bin/codium")


  /* platform info */

  sealed case class Platform_Info(
    platform: Platform.Family.Value,
    download_template: String,
    build_name: String,
    env: List[String])
  {
    def download_name: String = "VSCodium-" + download_template.replace("{VERSION}", version)
    def download_zip: Boolean = download_name.endsWith(".zip")

    def download(dir: Path, progress: Progress = new Progress): Unit =
    {
      if (download_zip) Isabelle_System.require_command("unzip", test = "-h")

      Isabelle_System.with_tmp_file("download")(download_file =>
      {
        Isabelle_System.download_file(vscodium_download + "/" + version + "/" + download_name,
          download_file, progress = progress)

        progress.echo("Unpacking " + dir.expand)
        if (download_zip) {
          Isabelle_System.bash("unzip -x " + File.bash_path(download_file), cwd = dir.file).check
        }
        else {
          Isabelle_System.gnutar("-xzf " + File.bash_path(download_file), dir = dir).check
        }
      })
    }

    def platform_dir(dir: Path): Path =
    {
      val platform_name =
        if (platform == Platform.Family.windows) Platform.Family.native(platform)
        else Platform.Family.standard(platform)
      dir + Path.explode(platform_name)
    }

    def build_dir(dir: Path): Path = dir + Path.explode(build_name)

    def build_environment: String =
      (("MS_TAG=" + Bash.string(version)) :: "SHOULD_BUILD=yes" :: "VSCODE_ARCH=x64" :: env)
        .map(s => "export " + s + "\n").mkString

    def resources_dir(dir: Path): Path =
    {
      val resources =
        if (platform == Platform.Family.macos) "VSCodium.app/Contents/Resources"
        else "resources"
      dir + Path.explode(resources)
    }

    def patch_resources(base_dir: Path): Unit =
    {
      val dir = resources_dir(base_dir)

      HTML.init_fonts(dir + Path.explode("app/out/vs/base/browser/ui"))

      val workbench_css = dir + Path.explode("app/out/vs/workbench/workbench.desktop.main.css")
      val checksum1 = file_checksum(workbench_css)
      File.append(workbench_css, "\n\n" + HTML.fonts_css_dir(prefix = "../base/browser/ui"))
      val checksum2 = file_checksum(workbench_css)

      val file_name = workbench_css.file_name
      File.change_lines(dir + Path.explode("app/product.json")) { _.map(line =>
        if (line.containsSlice(file_name) && line.contains(checksum1)) {
          line.replace(checksum1, checksum2)
        }
        else line)
      }
    }

    def setup_executables(dir: Path): Unit =
    {
      val exe = vscodium_exe(dir)
      Isabelle_System.make_directory(exe.dir)

      platform match {
        case Platform.Family.macos =>
          File.write(exe, macos_exe)
          File.set_executable(exe, true)
        case Platform.Family.windows =>
          val files1 = File.find_files(exe.dir.file)
          val files2 = File.find_files(dir.file, pred = file =>
            {
              val name = file.getName
              name.endsWith(".dll") || name.endsWith(".exe") || name.endsWith(".node")
            })
          for (file <- files1 ::: files2) File.set_executable(File.path(file), true)
          Isabelle_System.bash("chmod -R o-w " + File.bash_path(dir))
        case _ =>
      }
    }
  }

  // see https://github.com/microsoft/vscode/blob/main/build/gulpfile.vscode.js
  // function computeChecksum(filename)
  private def file_checksum(path: Path): String =
  {
    val digest = MessageDigest.getInstance("MD5")
    digest.update(Bytes.read(path).array)
    Bytes(Base64.getEncoder.encode(digest.digest()))
      .text.replaceAll("=", "")
  }

  private val platform_infos: Map[Platform.Family.Value, Platform_Info] =
    Iterator(
      Platform_Info(Platform.Family.linux, "linux-x64-{VERSION}.tar.gz", "VSCode-linux-x64",
        List("OS_NAME=linux", "SKIP_LINUX_PACKAGES=True")),
      Platform_Info(Platform.Family.linux_arm, "linux-arm64-{VERSION}.tar.gz", "VSCode-linux-arm64",
        List("OS_NAME=linux", "SKIP_LINUX_PACKAGES=True", "VSCODE_ARCH=arm64")),
      Platform_Info(Platform.Family.macos, "darwin-x64-{VERSION}.zip", "VSCode-darwin-x64",
        List("OS_NAME=osx")),
      Platform_Info(Platform.Family.windows, "win32-x64-{VERSION}.zip", "VSCode-win32-x64",
        List("OS_NAME=windows",
          "SHOULD_BUILD_ZIP=no",
          "SHOULD_BUILD_EXE_SYS=no",
          "SHOULD_BUILD_EXE_USR=no",
          "SHOULD_BUILD_MSI=no",
          "SHOULD_BUILD_MSI_NOUP=no")))
      .map(info => info.platform -> info).toMap

  def the_platform_info(platform: Platform.Family.Value): Platform_Info =
    platform_infos.getOrElse(platform, error("No platform info for " + quote(platform.toString)))


  /* check system */

  def check_system(platforms: List[Platform.Family.Value]): Unit =
  {
    Linux.check_system()

    Isabelle_System.require_command("git")
    if (platforms.nonEmpty) {
      Isabelle_System.require_command("node")
      Isabelle_System.require_command("yarn")
      Isabelle_System.require_command("jq")
    }
    if (platforms.contains(Platform.Family.windows)) {
      Isabelle_System.require_command("wine")
    }
    if (platforms.exists(platform => the_platform_info(platform).download_zip)) {
      Isabelle_System.require_command("unzip", test = "-h")
    }
  }


  /* build vscodium */

  def default_platforms: List[Platform.Family.Value] = Platform.Family.list

  def macos_exe: String =
"""#!/usr/bin/env bash

unset CDPATH
VSCODE_PATH="$(cd "$(dirname "$0")"/../VSCodium.app/Contents; pwd)"

ELECTRON="$VSCODE_PATH/MacOS/Electron"
CLI="$VSCODE_PATH/Resources/app/out/cli.js"
ELECTRON_RUN_AS_NODE=1 "$ELECTRON" "$CLI" --ms-enable-electron-run-as-node "$@"
exit $?
"""

  def build_vscodium(
    target_dir: Path = Path.current,
    platforms: List[Platform.Family.Value] = default_platforms,
    verbose: Boolean = false,
    progress: Progress = new Progress): Unit =
  {
    check_system(platforms)


    /* component */

    val component_name = "vscodium-" + version
    val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component_name))
    progress.echo("Component " + component_dir)


    /* build */

    for (platform <- platforms) {
      val platform_info = the_platform_info(platform)

      progress.echo("Building " + platform + " ...")

      Isabelle_System.with_tmp_dir("vscodium")(vscodium_dir =>
      {
        def execute(lines: String*): Unit =
          progress.bash(("set -e" :: platform_info.build_environment :: lines.toList).mkString("\n"),
            cwd = vscodium_dir.file, echo = verbose).check

        execute(
          "git clone -n " + Bash.string(vscodium_repository) + " .",
          "git checkout -q " + Bash.string(version),
          "./get_repo.sh")

        for (name <- Seq("vscode/build/lib/electron.js", "vscode/build/lib/electron.ts")) {
          File.change(vscodium_dir + Path.explode(name), strict = true) {
            _.replace("""'resources/darwin/' + icon + '.icns'""",
              """'resources/darwin/' + icon.toLowerCase() + '.icns'""")
          }
        }

        execute("./build.sh")

        Isabelle_System.copy_file(vscodium_dir + Path.explode("LICENSE"), component_dir)

        val platform_dir = platform_info.platform_dir(component_dir)
        Isabelle_System.copy_dir(platform_info.build_dir(vscodium_dir), platform_dir)
        platform_info.patch_resources(platform_dir)
        platform_info.setup_executables(platform_dir)
      })
    }


    /* settings */

    val etc_dir = Isabelle_System.make_directory(component_dir + Path.explode("etc"))
    File.write(etc_dir + Path.basic("settings"),
      """# -*- shell-script -*- :mode=shellscript:

ISABELLE_VSCODIUM_HOME="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-$ISABELLE_PLATFORM64}"

case "$ISABELLE_PLATFORM_FAMILY" in
  linux)
    ISABELLE_ELECTRON="$ISABELLE_VSCODIUM_HOME/codium"
    ;;
  macos)
    ISABELLE_ELECTRON="$ISABELLE_VSCODIUM_HOME/VSCodium.app/Contents/MacOS/Electron"
    ;;
  windows)
    ISABELLE_ELECTRON="$ISABELLE_VSCODIUM_HOME/VSCodium.exe"
    ;;
esac
""")


    /* README */

    File.write(component_dir + Path.basic("README"),
      "This is VSCodium " + version + " from " + vscodium_repository +
"""

It has been built from sources using "isabelle build_vscodium": this applies
a few changes required for Isabelle/VSCode.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_vscodium", "build component for VSCodium",
      Scala_Project.here, args =>
    {
      var target_dir = Path.current
      var platforms = default_platforms
      var verbose = false

      val getopts = Getopts("""
Usage: vscode_setup [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -p NAMES     platform families (default: """ + quote(platforms.mkString(",")) + """)
    -v           verbose

  Build VSCodium from sources and turn it into an Isabelle component.

  The build platform needs to be Linux with nodejs/yarn, jq, and wine
  for targeting Windows.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "p:" -> (arg => platforms = Library.space_explode(',', arg).map(Platform.Family.parse)),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      build_vscodium(target_dir = target_dir, platforms = platforms,
        verbose = verbose, progress = progress)
    })
}
