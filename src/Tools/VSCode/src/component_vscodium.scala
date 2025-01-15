/*  Title:      Tools/VSCode/src/component_vscodium.scala
    Author:     Makarius

Build the Isabelle system component for VSCodium: cross-compilation for all
platforms.
*/

package isabelle.vscode


import isabelle._

import java.security.MessageDigest
import java.util.Base64


object Component_VSCodium {
  /* global parameters */

  lazy val version: String = Isabelle_System.getenv_strict("ISABELLE_VSCODE_VERSION")
  val vscodium_repository = "https://github.com/VSCodium/vscodium.git"
  val vscodium_download = "https://github.com/VSCodium/vscodium/releases/download"

  private val resources = Path.explode("resources")


  /* Isabelle symbols (static subset only) */

  lazy val symbols: Symbol.Symbols =
    Symbol.Symbols.make(File.read(Path.explode("~~/etc/symbols")))

  def make_symbols(): File.Content = {
    val symbols_js =
      JSON.Format.pretty_print(
        for (entry <- symbols.entries) yield
          JSON.Object(
            "symbol" -> entry.symbol,
            "name" -> entry.name,
            "abbrevs" -> entry.abbrevs) ++
          JSON.optional("code", entry.code))

    File.content(Path.explode("symbols.json"), symbols_js)
  }

  def make_isabelle_encoding(header: String): File.Content = {
    val symbols_js =
      JSON.Format.pretty_print(
        for (entry <- symbols.entries; code <- entry.code)
          yield JSON.Object("symbol" -> entry.symbol, "code" -> code))

    val path = Path.explode("isabelle_encoding.ts")
    val body =
      File.read(Path.explode("$ISABELLE_VSCODE_HOME/patches") + path)
        .replace("[/*symbols*/]", symbols_js)
    File.content(path, header + "\n" + body)
  }


  /* platform info */

  sealed case class Platform_Info(
    platform: Platform.Family,
    download_template: String,
    build_name: String,
    env: List[String]
  ) {
    def primary: Boolean = platform == Platform.Family.linux

    def download_name: String = "VSCodium-" + download_template.replace("{VERSION}", version)
    def download_ext: String = if (download_template.endsWith(".zip")) "zip" else "tar.gz"

    def download(dir: Path, progress: Progress = new Progress): Unit = {
      Isabelle_System.with_tmp_file("download", ext = download_ext) { download_file =>
        Isabelle_System.download_file(vscodium_download + "/" + version + "/" + download_name,
          download_file, progress = progress)

        progress.echo("Extract ...")
        Isabelle_System.extract(download_file, dir)
      }
    }

    def get_vscodium_repository(build_dir: Path, progress: Progress = new Progress): Unit = {
      progress.echo("Getting VSCodium repository ...")
      Isabelle_System.git_clone(vscodium_repository, build_dir, checkout = version)

      progress.echo("Getting VSCode repository ...")
      Isabelle_System.bash(environment + "\n" + "./get_repo.sh", cwd = build_dir).check
    }

    def platform_dir(dir: Path): Path = {
      val platform_name =
        if (platform == Platform.Family.windows) Platform.Family.native(platform)
        else Platform.Family.standard(platform)
      dir + Path.explode(platform_name)
    }

    def build_dir(dir: Path): Path = dir + Path.explode(build_name)

    def environment: String =
      (("MS_TAG=" + Bash.string(version)) :: "SHOULD_BUILD=yes" :: "VSCODE_ARCH=x64" :: env)
        .map(s => "export " + s + "\n").mkString

    def patch_sources(base_dir: Path): String = {
      val dir = base_dir + Path.explode("vscode")
      Isabelle_System.with_copy_dir(dir, dir.orig) {
        // macos icns
        for (name <- Seq("build/lib/electron.js", "build/lib/electron.ts")) {
          File.change(dir + Path.explode(name), strict = true) {
            _.replace("""'resources/darwin/' + icon + '.icns'""",
              """'resources/darwin/' + icon.toLowerCase() + '.icns'""")
          }
        }

        // isabelle_encoding.ts
        {
          val common_dir = dir + Path.explode("src/vs/workbench/services/textfile/common")
          val header =
            split_lines(File.read(common_dir + Path.explode("encoding.ts")))
              .takeWhile(_.trim.nonEmpty)
          make_isabelle_encoding(cat_lines(header)).write(common_dir)
        }

        // explicit patches
        {
          val patches_dir = Path.explode("$ISABELLE_VSCODE_HOME/patches")
          for (name <- Seq("cli", "isabelle_encoding", "no_ocaml_icons")) {
            val path = patches_dir + Path.explode(name).patch
            Isabelle_System.bash("patch -p1 < " + File.bash_path(path), cwd = dir).check
          }
        }

        Isabelle_System.make_patch(base_dir, dir.base.orig, dir.base)
      }
    }

    def patch_resources(base_dir: Path): String = {
      val dir = base_dir + resources
      val patch =
        Isabelle_System.with_copy_dir(dir, dir.orig) {
          val fonts_dir = dir + Path.explode("app/out/vs/base/browser/ui/fonts")
          HTML.init_fonts(fonts_dir.dir)
          make_symbols().write(fonts_dir)

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

          Isabelle_System.make_patch(dir.dir, dir.orig.base, dir.base)
        }

      val app_dir = dir + Path.explode("app")
      val vscodium_app_dir = dir + Path.explode("vscodium")
      Isabelle_System.move_file(app_dir, vscodium_app_dir)

      Isabelle_System.make_directory(app_dir)
      if ((vscodium_app_dir + resources).is_dir) {
        Isabelle_System.copy_dir(vscodium_app_dir + resources, app_dir)
      }

      patch
    }

    def init_resources(base_dir: Path): Path = {
      val dir = base_dir + resources
      if (platform == Platform.Family.macos) {
        Isabelle_System.symlink(Path.explode("VSCodium.app/Contents/Resources"), dir)
      }
      dir
    }

    def setup_node(target_dir: Path, progress: Progress): Unit = {
      Isabelle_System.with_tmp_dir("download") { download_dir =>
        download(download_dir, progress = progress)
        val dir1 = init_resources(download_dir)
        val dir2 = init_resources(target_dir)
        for (name <- Seq("app/node_modules.asar", "app/node_modules.asar.unpacked")) {
          val path = Path.explode(name)
          Isabelle_System.rm_tree(dir2 + path)
          Isabelle_System.copy_dir(dir1 + path, dir2 + path)
        }
      }
    }

    def setup_electron(dir: Path): Unit = {
      val electron = Path.explode("electron")
      platform match {
        case Platform.Family.linux | Platform.Family.linux_arm =>
          Isabelle_System.move_file(dir + Path.explode("codium"), dir + electron)
        case Platform.Family.windows =>
          Isabelle_System.move_file(dir + Path.explode("VSCodium.exe"), dir + electron.exe)
          Isabelle_System.move_file(
            dir + Path.explode("VSCodium.VisualElementsManifest.xml"),
            dir + Path.explode("electron.VisualElementsManifest.xml"))
        case Platform.Family.macos =>
      }
    }

    def setup_executables(dir: Path): Unit = {
      Isabelle_System.rm_tree(dir + Path.explode("bin"))

      if (platform == Platform.Family.windows) {
        val files =
          File.find_files(dir.file, pred = { file =>
            val name = file.getName
            File.is_dll(name) || File.is_exe(name) || File.is_node(name)
          })
        files.foreach(file => File.set_executable(File.path(file)))
        Isabelle_System.bash("chmod -R o-w " + File.bash_path(dir)).check
      }
    }
  }


  // see https://github.com/microsoft/vscode/blob/main/build/gulpfile.vscode.js
  // function computeChecksum(filename)
  private def file_checksum(path: Path): String = {
    val digest = MessageDigest.getInstance("MD5")
    digest.update(Bytes.read(path).make_array)
    Bytes(Base64.getEncoder.encode(digest.digest()))
      .text.replaceAll("=", "")
  }

  private val platform_infos: Map[Platform.Family, Platform_Info] =
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

  def the_platform_info(platform: Platform.Family): Platform_Info =
    platform_infos.getOrElse(platform, error("No platform info for " + quote(platform.toString)))

  def linux_platform_info: Platform_Info =
    the_platform_info(Platform.Family.linux)


  /* check system */

  def check_system(platforms: List[Platform.Family]): Unit = {
    if (Platform.family != Platform.Family.linux) error("Not a Linux/x86_64 system")

    Isabelle_System.require_command("git")
    Isabelle_System.require_command("node")
    Isabelle_System.require_command("yarn")
    Isabelle_System.require_command("jq")

    if (platforms.contains(Platform.Family.windows)) {
      Isabelle_System.require_command("wine")
    }
  }


  /* original repository clones and patches */

  def vscodium_patch(progress: Progress = new Progress): String = {
    val platform_info = linux_platform_info
    check_system(List(platform_info.platform))

    Isabelle_System.with_tmp_dir("build") { build_dir =>
      platform_info.get_vscodium_repository(build_dir, progress = progress)
      val vscode_dir = build_dir + Path.explode("vscode")
      progress.echo("Prepare ...")
      Isabelle_System.with_copy_dir(vscode_dir, vscode_dir.orig) {
        progress.bash(
          List(
            "set -e",
            platform_info.environment,
            "./prepare_vscode.sh",
            // enforce binary diff of code.xpm
            "cp vscode/resources/linux/code.png vscode/resources/linux/rpm/code.xpm"
          ).mkString("\n"), cwd = build_dir, echo = progress.verbose).check
        Isabelle_System.make_patch(build_dir, vscode_dir.orig.base, vscode_dir.base,
          diff_options = "--exclude=.git --exclude=node_modules")
      }
    }
  }


  /* build vscodium */

  def default_platforms: List[Platform.Family] = Platform.Family.list

  def component_vscodium(
    target_dir: Path = Path.current,
    platforms: List[Platform.Family] = default_platforms,
    progress: Progress = new Progress
  ): Unit = {
    check_system(platforms)


    /* component */

    val component_name = "vscodium-" + version
    val component_dir =
      Components.Directory(target_dir + Path.explode(component_name)).create(progress = progress)


    /* patches */

    progress.echo("\n* Building patches:")

    val patches_dir = Isabelle_System.new_directory(component_dir.path + Path.explode("patches"))

    def write_patch(name: String, patch: String): Unit =
      File.write(patches_dir + Path.explode(name).patch, patch)

    write_patch("01-vscodium", vscodium_patch(progress = progress))


    /* build */

    for (platform <- platforms) yield {
      val platform_info = the_platform_info(platform)

      Isabelle_System.with_tmp_dir("build") { build_dir =>
        progress.echo("\n* Building " + platform + ":")

        platform_info.get_vscodium_repository(build_dir, progress = progress)

        val sources_patch = platform_info.patch_sources(build_dir)
        if (platform_info.primary) write_patch("02-isabelle_sources", sources_patch)

        progress.echo("Build ...")
        progress.bash(platform_info.environment + "\n" + "./build.sh",
          cwd = build_dir, echo = progress.verbose).check

        if (platform_info.primary) {
          Isabelle_System.copy_file(build_dir + Path.explode("LICENSE"), component_dir.path)
        }

        val platform_dir = platform_info.platform_dir(component_dir.path)
        Isabelle_System.copy_dir(platform_info.build_dir(build_dir), platform_dir)
        platform_info.setup_node(platform_dir, progress)
        platform_info.setup_electron(platform_dir)

        val resources_patch = platform_info.patch_resources(platform_dir)
        if (platform_info.primary) write_patch("03-isabelle_resources", resources_patch)

        Isabelle_System.copy_file(
          build_dir + Path.explode("vscode/node_modules/electron/dist/resources/default_app.asar"),
          platform_dir + resources)

        platform_info.setup_executables(platform_dir)
      }
    }

    Isabelle_System.bash("gzip *.patch", cwd = patches_dir).check


    /* settings */

    component_dir.write_settings("""
ISABELLE_VSCODIUM_HOME="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-$ISABELLE_PLATFORM64}"

case "$ISABELLE_PLATFORM_FAMILY" in
  "macos"*)
    ISABELLE_VSCODIUM_ELECTRON="$ISABELLE_VSCODIUM_HOME/VSCodium.app/Contents/MacOS/Electron"
    ISABELLE_VSCODIUM_RESOURCES="$ISABELLE_VSCODIUM_HOME/VSCodium.app/Contents/Resources"
    ;;
  *)
    ISABELLE_VSCODIUM_ELECTRON="$ISABELLE_VSCODIUM_HOME/electron"
    ISABELLE_VSCODIUM_RESOURCES="$ISABELLE_VSCODIUM_HOME/resources"
    ;;
esac
""")


    /* README */

    File.write(component_dir.README,
      "This is VSCodium " + version + " from " + vscodium_repository +
"""

It has been built from sources using "isabelle component_vscodium". This applies
a few changes required for Isabelle/VSCode, see "patches" directory for a
formal record.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrappers */

  val isabelle_tool1 =
    Isabelle_Tool("component_vscodium", "build component for VSCodium",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var platforms = default_platforms
        var verbose = false

        val getopts = Getopts("""
Usage: component_vscodium [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -p NAMES     platform families (default: """ + quote(platforms.mkString(",")) + """)
    -v           verbose

  Build VSCodium from sources and turn it into an Isabelle component.

  The build platform needs to be Linux with nodejs/yarn, jq, and wine
  for targeting Windows.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "p:" -> (arg => platforms = space_explode(',', arg).map(Platform.Family.parse)),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        component_vscodium(target_dir = target_dir, platforms = platforms, progress = progress)
      })

  val isabelle_tool2 =
    Isabelle_Tool("vscode_patch", "patch VSCode source tree",
      Scala_Project.here,
      { args =>
        var base_dir = Path.current

        val getopts = Getopts("""
Usage: vscode_patch [OPTIONS]

  Options are:
    -D DIR       base directory (default ".")

  Patch original VSCode source tree for use with Isabelle/VSCode.
""",
          "D:" -> (arg => base_dir = Path.explode(arg)))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val platform_info = the_platform_info(Platform.family)
        platform_info.patch_sources(base_dir)
      })
}
