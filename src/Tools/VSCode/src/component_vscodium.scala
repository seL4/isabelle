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
  /* platform prerequisites */

  val linux_packages: List[String] =
    List(
      "jq", "git", "python3", "gcc", "g++", "make", "pkg-config", "fakeroot",
      "libx11-dev", "libxkbfile-dev", "libsecret-1-dev", "libkrb5-dev")

  val windows_packages_msys2: List[String] =
    List("p7zip", "git", "jq", "mingw-w64-ucrt-x86_64-rustup")

  val macos_packages: List[String] =
    List("jq")


  /* vscode parameters */

  val default_node_version = Nodejs.default_version
  val default_vscodium_version = "1.103.25610"

  val vscodium_repository = "https://github.com/VSCodium/vscodium.git"
  val vscodium_download = "https://github.com/VSCodium/vscodium/releases/download"

  def vscode_arch(platform_context: Isabelle_Platform.Context): String =
    if (platform_context.is_arm) "arm64" else "x64"

  def vscode_os_name(platform_context: Isabelle_Platform.Context): String =
    if (platform_context.isabelle_platform.is_windows) "windows"
    else if (platform_context.isabelle_platform.is_macos) "osx"
    else "linux"

  def vscode_platform_name(platform_context: Isabelle_Platform.Context): String =
    if (platform_context.isabelle_platform.is_windows) "win32"
    else if (platform_context.isabelle_platform.is_macos) "darwin"
    else "linux"

  def vscode_platform(platform_context: Isabelle_Platform.Context): String =
    vscode_platform_name(platform_context) + "-" + vscode_arch(platform_context)

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

  object Build_Context {
    def make(
      platform_context: Isabelle_Platform.Context,
      node_root: Option[Path] = None,
      node_version: String = "",
      vscodium_version: String = default_vscodium_version
    ): Build_Context = {
      val platform = platform_context.isabelle_platform
      val env1 =
        List(
          "OS_NAME=" + vscode_os_name(platform_context),
          "VSCODE_ARCH=" + vscode_arch(platform_context))
      val env2 =
        if (platform.is_windows) {
          List(
            "SHOULD_BUILD_ZIP=no",
            "SHOULD_BUILD_EXE_SYS=no",
            "SHOULD_BUILD_EXE_USR=no",
            "SHOULD_BUILD_MSI=no",
            "SHOULD_BUILD_MSI_NOUP=no",
            "-ISABELLE_CLASSPATH",
            "-ISABELLE_COMPONENTS",
            "-ISABELLE_FONTS",
            "-ISABELLE_SETUP_CLASSPATH",
            "-JEDIT_JARS",
            "-JORTHO_DICTIONARIES",
            "-KODKODI_CLASSPATH",
            "-SOLR_JARS") ::: Isabelle_System.no_bash_functions
        }
        else if (platform.is_linux) List("SKIP_LINUX_PACKAGES=True")
        else Nil
      val node_version1 = proper_string(node_version).getOrElse(default_node_version)
      new Build_Context(platform_context, node_root, node_version1, vscodium_version, env1 ::: env2)
    }
  }

  class Build_Context private(
    val platform_context: Isabelle_Platform.Context,
    node_root: Option[Path],
    node_version: String,
    vscodium_version: String,
    env: List[String]
  ) {
    override def toString: String = platform_name

    def platform: Isabelle_Platform = platform_context.isabelle_platform
    def progress: Progress = platform_context.progress

    def node_setup(base_dir: Path): Nodejs.Directory =
      node_root match {
        case Some(path) => Nodejs.directory(platform_context, path)
        case None =>
          Nodejs.setup(base_dir,
            platform_context = platform_context,
            version = node_version,
            packages = List("yarn"))
      }

    def download_ext: String = if (platform.is_linux) "tar.gz" else "zip"

    def download_name: String =
      "VSCodium-" + vscode_platform(platform_context) + "-" + vscodium_version + "." + download_ext

    def download(dir: Path): Unit = {
      Isabelle_System.with_tmp_file("download", ext = download_ext) { download_file =>
        progress.echo("Getting VSCodium release ...")
        Isabelle_System.download_file(vscodium_download + "/" + vscodium_version + "/" + download_name,
          download_file)
        Isabelle_System.extract(download_file, dir)
      }
    }

    def get_vscodium_repository(build_dir: Path): Unit = {
      progress.echo("Getting VSCodium repository ...")
      Isabelle_System.git_clone(vscodium_repository, build_dir, checkout = vscodium_version)

      progress.echo("Getting VSCode repository ...")
      platform_context.execute(build_dir, environment(build_dir) + "\n" + "./get_repo.sh").check
    }

    def platform_name: String = platform_context.ISABELLE_PLATFORM
    def platform_dir(dir: Path): Path = dir + Path.explode(platform_name)

    def build_dir(dir: Path): Path = dir + Path.basic("VSCode-" + vscode_platform(platform_context))

    def environment(dir: Path): String =
      Bash.exports((build_env ::: build_upstream_env(dir) ::: env):_*)

    def patch_sources(base_dir: Path): String = {
      val dir = base_dir + Path.explode("vscode")
      Isabelle_System.with_copy_dir(dir, dir.orig) {
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

    def setup_electron(dir: Path): Unit = {
      val electron = Path.explode("electron")
      if (platform.is_linux) {
        Isabelle_System.move_file(dir + Path.explode("codium"), dir + electron)
      }
      else if (platform.is_windows) {
        Isabelle_System.move_file(dir + Path.explode("VSCodium.exe"), dir + electron.exe)
        Isabelle_System.move_file(
          dir + Path.explode("VSCodium.VisualElementsManifest.xml"),
          dir + Path.explode("electron.VisualElementsManifest.xml"))
      }
    }

    def setup_executables(dir: Path): Unit = {
      Isabelle_System.rm_tree(dir + Path.explode("bin"))

      if (platform.is_windows) {
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


  /* original repository clones and patches */

  def vscodium_patch(build_context: Build_Context): String = {
    val platform_context = build_context.platform_context
    val progress = build_context.progress

    Isabelle_System.with_tmp_dir("build") { build_dir =>
      build_context.get_vscodium_repository(build_dir)
      val vscode_dir = build_dir + Path.explode("vscode")

      val node_dir = build_context.node_setup(build_dir)

      progress.echo("Preparing VSCode ...")
      Isabelle_System.with_copy_dir(vscode_dir, vscode_dir.orig) {
        platform_context.execute(build_dir,
          "set -e",
          build_context.environment(build_dir),
          node_dir.path_setup,
          "./prepare_vscode.sh",
          // enforce binary diff of code.xpm
          "cp vscode/resources/linux/code.png vscode/resources/linux/rpm/code.xpm").check
        Isabelle_System.make_patch(build_dir, vscode_dir.orig.base, vscode_dir.base,
          diff_options = "--exclude=.git --exclude=node_modules")
      }
    }
  }


  /* build vscodium */

  def component_vscodium(
    target_dir: Path = Path.current,
    node_root: Option[Path] = None,
    node_version: String = default_node_version,
    vscodium_version: String = default_vscodium_version,
    platform_context: Isabelle_Platform.Context = Isabelle_Platform.Context(),
  ): Unit = {
    val platform = platform_context.isabelle_platform
    val progress = platform_context.progress

    val build_context =
      Build_Context.make(platform_context,
        node_root = node_root,
        node_version = node_version,
        vscodium_version = vscodium_version)

    platform_context.mingw.check()

    Isabelle_System.require_command("patch")
    if (!platform.is_windows) {
      Isabelle_System.require_command("git")
      Isabelle_System.require_command("jq")
      Isabelle_System.require_command("rustup")
    }


    /* component */

    val component_name = "vscodium-" + vscodium_version
    val component_dir =
      Components.Directory(target_dir + Path.explode(component_name)).create(progress = progress)


    /* patches */

    progress.echo("\n* Building patches:")

    val patches_dir = Isabelle_System.new_directory(component_dir.path + Path.explode("patches"))

    def write_patch(name: String, patch: String): Unit =
      File.write(patches_dir + Path.explode(name).patch, patch)

    write_patch("01-vscodium", vscodium_patch(build_context))


    /* build */

    Isabelle_System.with_tmp_dir("build") { build_dir =>
      progress.echo("\n* Building VSCodium for " + build_context.platform_name + ":")

      build_context.get_vscodium_repository(build_dir)
      Isabelle_System.apply_patch(build_dir, read_patch("vscodium"), progress = progress)

      val sources_patch = build_context.patch_sources(build_dir)
      write_patch("02-isabelle_sources", sources_patch)

      val node_dir = build_context.node_setup(build_dir)

      progress.echo("Building VSCodium ...")
      val environment = build_context.environment(build_dir)
      progress.echo(environment, verbose = true)
      platform_context.execute(
        build_dir, node_dir.path_setup + "\n" + environment + "./build.sh").check

      Isabelle_System.copy_file(build_dir + Path.explode("LICENSE"), component_dir.path)

      val platform_dir = build_context.platform_dir(component_dir.path)
      Isabelle_System.copy_dir(build_context.build_dir(build_dir), platform_dir)
      if (platform.is_macos) {
        Isabelle_System.symlink(Path.explode("VSCodium.app/Contents/Resources"),
          platform_dir + resources)
      }
      build_context.setup_electron(platform_dir)

      val resources_patch = build_context.patch_resources(platform_dir)
      write_patch("03-isabelle_resources", resources_patch)

      val electron_resources =
        Path.explode("vscode/node_modules/electron/dist") +
          (if (platform.is_macos) Path.explode("Electron.app/Contents/Resources") else resources)
      Isabelle_System.copy_file(
        build_dir + electron_resources + Path.explode("default_app.asar"),
        platform_dir + resources)

      build_context.setup_executables(platform_dir)
    }

    Isabelle_System.bash("gzip *.patch", cwd = patches_dir).check


    /* settings */

    component_dir.write_settings("""
ISABELLE_VSCODIUM_HOME="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}}"

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
formal record. Typical build commands for special platforms are as follows.

* x86_64-darwin on Apple Silicon hardware:

    isabelle component_vscodium -I

* x86_64-windows with Cygwin-Terminal, using prerequisites in typical locations:

    export NODE_GYP_FORCE_PYTHON='C:\Python313\python.exe'
    isabelle component_vscodium -M "/cygdrive/c/msys64" -n "/cygdrive/c/Program Files/nodejs"


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrappers */

  val isabelle_tool1 =
    Isabelle_Tool("component_vscodium", "build component for VSCodium",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var intel = false
        var mingw = MinGW.none
        var node_version = default_node_version
        var vscodium_version = default_vscodium_version
        var node_root: Option[Path] = None
        var verbose = false

        val getopts = Getopts("""
Usage: component_vscodium [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -I           force Intel platform on Apple Silicon
    -M DIR       msys/mingw root specification for Windows
    -N VERSION   download Node.js version (overrides option -n)
                 (default: """" + default_node_version + """")
    -V VERSION   VSCodium version (default: """" + default_vscodium_version + """")
    -n DIR       use existing Node.js directory (overrides option -N)
    -v           verbose

  Build VSCodium from sources and turn it into an Isabelle component.

  Linux prerequisites:
    - Ubuntu 20.04 LTS
    - rustup: see https://www.rust-lang.org/tools/install
    - apt packages:
      sudo apt install -y """ + linux_packages.mkString(" ") + """

  Windows prerequisites:
    - install Visual Studio 2022 with C++ development and C++ library with
      Spectre mitigation: see https://visualstudio.microsoft.com/downloads
    - install Nodejs """ + default_node_version + """ including Windows build tools:
      see https://nodejs.org/dist/v""" + default_node_version +
        "/node-v" + default_node_version + """-x64.msi
    - rebuild native node-pty, using "cmd" as Administrator:
        npm install --global node-gyp node-pty@1.1.0-beta33
        cd "C:\Program Files\nodejs\node_modules\node-pty"
        npx node-gyp rebuild node-pty
    - MSYS2/UCRT64: see https://www.msys2.org
    - MSYS2 packages:
      pacman -Su
      pacman -S --needed --noconfirm """ + windows_packages_msys2.mkString(" ") + """

  macOS prerequisites:
    - rustup: see https://www.rust-lang.org/tools/install
    - Homebrew package manager: see https://brew.sh
    - Homebrew packages:
      brew install """ + macos_packages.mkString(" ") + """
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "I" -> (arg => intel = true),
          "M:" -> (arg => mingw = MinGW(Path.explode(arg))),
          "N:" -> { arg => node_version = arg; node_root = None },
          "V:" -> (arg => vscodium_version = arg),
          "n:" -> { arg => node_root = Some(Path.explode(arg)); node_version = "" },
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)
        val platform_context = Isabelle_Platform.Context(mingw = mingw, apple = !intel, progress = progress)

        component_vscodium(target_dir = target_dir, node_root = node_root,
          node_version = node_version, vscodium_version = vscodium_version,
          platform_context = platform_context)
      })

  val isabelle_tool2 =
    Isabelle_Tool("vscode_patch", "patch VSCode source tree",
      Scala_Project.here,
      { args =>
        var base_dir = Path.current
        var mingw = MinGW.none
        var verbose = false

        val getopts = Getopts("""
Usage: vscode_patch [OPTIONS]

  Options are:
    -D DIR       base directory (default ".")
    -M DIR       msys/mingw root specification for Windows
    -v           verbose

  Patch original VSCode source tree for use with Isabelle/VSCode.
""",
          "D:" -> (arg => base_dir = Path.explode(arg)),
          "M:" -> (arg => mingw = MinGW(Path.explode(arg))),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)
        val platform_context = Isabelle_Platform.Context(mingw = mingw, progress = progress)

        Build_Context.make(platform_context).patch_sources(base_dir)
      })
}
