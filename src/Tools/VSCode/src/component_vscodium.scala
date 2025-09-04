/*  Title:      Tools/VSCode/src/component_vscodium.scala
    Author:     Makarius

Build the Isabelle system component for VSCodium: cross-compilation for all
platforms.

See also https://github.com/VSCodium/vscodium/blob/master/docs/howto-build.md
*/

package isabelle.vscode


import isabelle._

import java.security.MessageDigest
import java.util.Base64


object Component_VSCodium {
  /* global parameters */

  val vscodium_version = "1.103.25610"
  val vscodium_repository = "https://github.com/VSCodium/vscodium.git"
  val vscodium_download = "https://github.com/VSCodium/vscodium/releases/download"

  def vscode_arch(platform: Platform.Family): String =
    if (platform == Platform.Family.linux_arm) "arm64" else "x64"

  def vscode_os_name(platform: Platform.Family): String =
    platform match {
      case Platform.Family.linux | Platform.Family.linux_arm => "linux"
      case Platform.Family.macos => "osx"
      case Platform.Family.windows => "windows"
    }

  def vscode_platform_name(platform: Platform.Family): String =
    platform match {
      case Platform.Family.linux | Platform.Family.linux_arm => "linux"
      case Platform.Family.macos => "darwin"
      case Platform.Family.windows => "win32"
    }

  def vscode_platform(platform: Platform.Family): String =
    vscode_platform_name(platform) + "-" + vscode_arch(platform)

  private val resources = Path.explode("resources")

  private def read_patch(name: String): String =
    File.read(Path.explode("$ISABELLE_VSCODE_HOME/patches") + Path.basic(name).patch)


  /* build environment */

  val build_env: List[String] =
    List(
      "VSCODE_QUALITY=stable",
      "VSCODE_LATEST=no",
      "CI_BUILD=no",
      "SKIP_ASSETS=yes",
      "SHOULD_BUILD=yes",
      "SHOULD_BUILD_REH=no",
      "SHOULD_BUILD_REH_WEB=no")

  def build_upstream_env(dir: Path): List[String] = {
    val str = File.read(dir + Path.explode("upstream/stable.json"))
    val json = JSON.parse(str)
    (for {
      tag <- JSON.string(json, "tag")
      commit <- JSON.string(json, "commit")
    } yield List("MS_TAG=" + tag, "MS_COMMIT=" + commit))
      .getOrElse(error("Malformed upstream information:\n" + str))
  }


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


  /* platform-specific build context */

  def platform_build_context(platform: Platform.Family): Build_Context = {
    val env1 =
      List(
        "OS_NAME=" + vscode_os_name(platform),
        "VSCODE_ARCH=" + vscode_arch(platform))
    val env2 =
      platform match {
        case Platform.Family.linux | Platform.Family.linux_arm =>
          List("SKIP_LINUX_PACKAGES=True")
        case Platform.Family.macos => Nil
        case Platform.Family.windows =>
          List(
            "SHOULD_BUILD_ZIP=no",
            "SHOULD_BUILD_EXE_SYS=no",
            "SHOULD_BUILD_EXE_USR=no",
            "SHOULD_BUILD_MSI=no",
            "SHOULD_BUILD_MSI_NOUP=no")
      }
    Build_Context(platform, env1 ::: env2)
  }

  sealed case class Build_Context(platform: Platform.Family, env: List[String]) {
    def primary_platform: Boolean = platform == Platform.Family.linux

    def download_ext: String =
      if (platform == Platform.Family.windows) ".zip" else ".tar.gz"

    def download_name: String =
      "VSCodium-" + vscode_platform(platform) + "-" + vscodium_version + download_ext

    def download(dir: Path, progress: Progress = new Progress): Unit = {
      Isabelle_System.with_tmp_file("download", ext = download_ext) { download_file =>
        Isabelle_System.download_file(vscodium_download + "/" + vscodium_version + "/" + download_name,
          download_file, progress = progress)

        progress.echo("Extract ...")
        Isabelle_System.extract(download_file, dir)
      }
    }

    def get_vscodium_repository(build_dir: Path, progress: Progress = new Progress): Unit = {
      progress.echo("Getting VSCodium repository ...")
      Isabelle_System.git_clone(vscodium_repository, build_dir, checkout = vscodium_version)

      progress.echo("Getting VSCode repository ...")
      Isabelle_System.bash(environment(build_dir) + "\n" + "./get_repo.sh", cwd = build_dir).check
    }

    def platform_dir(dir: Path): Path = {
      val platform_name =
        if (platform == Platform.Family.windows) Platform.Family.native(platform)
        else Platform.Family.standard(platform)
      dir + Path.explode(platform_name)
    }

    def build_dir(dir: Path): Path = dir + Path.basic("VSCode-" + vscode_platform(platform))

    def environment(dir: Path): String =
      (build_env ::: build_upstream_env(dir) ::: env)
        .map(s => "export " + s + "\n").mkString

    def patch_sources(base_dir: Path, progress: Progress = new Progress): String = {
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
        for (name <- Seq("cli", "isabelle_encoding", "no_ocaml_icons")) {
          Isabelle_System.apply_patch(dir, read_patch(name), progress = progress)
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
        for (name <- Seq("app/node_modules", "app/node_modules.asar")) {
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
    val digest = MessageDigest.getInstance("SHA-256")
    digest.update(Bytes.read(path).make_array)
    Bytes(Base64.getEncoder.encode(digest.digest()))
      .text.replaceAll("=", "")
  }


  /* check system */

  def check_system(platforms: List[Platform.Family]): Unit = {
    if (Platform.family != Platform.Family.linux) error("Not a Linux/x86_64 system")

    Isabelle_System.require_command("git")
    Isabelle_System.require_command("node")
    Isabelle_System.require_command("yarn")
    Isabelle_System.require_command("jq")
    Isabelle_System.require_command("rustup")

    if (platforms.contains(Platform.Family.windows)) {
      Isabelle_System.require_command("wine")
    }
  }


  /* original repository clones and patches */

  def vscodium_patch(progress: Progress = new Progress): String = {
    val build_context = platform_build_context(Platform.Family.linux)
    check_system(List(build_context.platform))

    Isabelle_System.with_tmp_dir("build") { build_dir =>
      build_context.get_vscodium_repository(build_dir, progress = progress)
      val vscode_dir = build_dir + Path.explode("vscode")
      progress.echo("Prepare ...")
      Isabelle_System.with_copy_dir(vscode_dir, vscode_dir.orig) {
        progress.bash(
          Library.make_lines(
            "set -e",
            build_context.environment(build_dir),
            "./prepare_vscode.sh",
            // enforce binary diff of code.xpm
            "cp vscode/resources/linux/code.png vscode/resources/linux/rpm/code.xpm"
          ), cwd = build_dir, echo = progress.verbose).check
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

    val component_name = "vscodium-" + vscodium_version
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
      val build_context = platform_build_context(platform)

      Isabelle_System.with_tmp_dir("build") { build_dir =>
        progress.echo("\n* Building " + platform + ":")

        build_context.get_vscodium_repository(build_dir, progress = progress)
        Isabelle_System.apply_patch(build_dir, read_patch("vscodium"), progress = progress)

        val sources_patch = build_context.patch_sources(build_dir, progress = progress)
        if (build_context.primary_platform) write_patch("02-isabelle_sources", sources_patch)

        progress.echo("Build ...")
        val environment = build_context.environment(build_dir)
        progress.echo(environment, verbose = true)
        progress.bash(environment + "\n" + "./build.sh",
          cwd = build_dir, echo = progress.verbose).check

        if (build_context.primary_platform) {
          Isabelle_System.copy_file(build_dir + Path.explode("LICENSE"), component_dir.path)
        }

        val platform_dir = build_context.platform_dir(component_dir.path)
        Isabelle_System.copy_dir(build_context.build_dir(build_dir), platform_dir)
        build_context.setup_node(platform_dir, progress)
        build_context.setup_electron(platform_dir)

        val resources_patch = build_context.patch_resources(platform_dir)
        if (build_context.primary_platform) write_patch("03-isabelle_resources", resources_patch)

        Isabelle_System.copy_file(
          build_dir + Path.explode("vscode/node_modules/electron/dist/resources/default_app.asar"),
          platform_dir + resources)

        build_context.setup_executables(platform_dir)
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
      "This is VSCodium " + vscodium_version + " from " + vscodium_repository +
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
        var verbose = false

        val getopts = Getopts("""
Usage: vscode_patch [OPTIONS]

  Options are:
    -D DIR       base directory (default ".")
    -v           verbose

  Patch original VSCode source tree for use with Isabelle/VSCode.
""",
          "D:" -> (arg => base_dir = Path.explode(arg)),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        val build_context = platform_build_context(Platform.family)
        build_context.patch_sources(base_dir, progress = progress)
      })
}
