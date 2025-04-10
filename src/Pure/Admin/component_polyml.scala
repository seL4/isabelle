/*  Title:      Pure/Admin/component_polyml.scala
    Author:     Makarius

Build Poly/ML from sources.

Note: macOS 14 Sonoma requires "LDFLAGS=... -ld64".
*/

package isabelle


object Component_PolyML {
  /** platform information **/

  sealed case class Platform_Info(
    options: List[String] = Nil,
    setup: String = "",
    libs: Set[String] = Set.empty)

  private val platform_info = Map(
    "linux" ->
      Platform_Info(
        options = List("LDFLAGS=-Wl,-rpath,_DUMMY_"),
        libs = Set("libgmp")),
    "darwin" ->
      Platform_Info(
        options = List("CFLAGS=-O3", "CXXFLAGS=-O3", "LDFLAGS=-segprot POLY rwx rwx"),
        setup = "PATH=/usr/bin:/bin:/usr/sbin:/sbin",
        libs = Set("libpolyml", "libgmp")),
    "windows" ->
      Platform_Info(
        options =
          List("--host=x86_64-w64-mingw32", "CPPFLAGS=-I/mingw64/include", "--disable-windows-gui"),
        setup = MinGW.env_prefix,
        libs = Set("libgcc_s_seh", "libgmp", "libstdc++", "libwinpthread")))

  sealed case class Platform_Context(
    platform: Isabelle_Platform = Isabelle_Platform.self,
    mingw: MinGW = MinGW.none,
    progress: Progress = new Progress
  ) {
    def standard_path(path: Path): String = mingw.standard_path(path)

    def polyml(arch_64: Boolean): String =
      (if (arch_64) platform.arch_64 else platform.arch_64_32) + "-" + platform.os_name

    def sha1: String = platform.arch_64 + "-" + platform.os_name

    def bash(cwd: Path, script: String, redirect: Boolean = false): Process_Result = {
      val script1 =
        if (platform.is_arm && platform.is_macos) {
          "arch -arch arm64 bash -c " + Bash.string(script)
        }
        else mingw.bash_script(script)
      progress.bash(script1, cwd = cwd, redirect = redirect, echo = progress.verbose)
    }
  }



  /** build stages **/

  def make_polyml(
    platform_context: Platform_Context,
    root: Path,
    gmp_root: Option[Path] = None,
    sha1_root: Option[Path] = None,
    target_dir: Path = Path.current,
    arch_64: Boolean = false,
    options: List[String] = Nil
  ): Unit = {
    if (!((root + Path.explode("configure")).is_file && (root + Path.explode("PolyML")).is_dir))
      error("Bad Poly/ML root directory: " + root)

    val platform = platform_context.platform

    val info =
      platform_info.getOrElse(platform.os_name,
        error("Bad OS platform: " + quote(platform.os_name)))

    if (platform.is_linux) Isabelle_System.require_command("patchelf")


    /* configure and make */

    val configure_options = {
      val options1 =
        if (gmp_root.nonEmpty || platform.is_windows) List("--with-gmp")
        else List("--without-gmp")

      val options2 =
        for (opt <- info.options) yield {
          if (opt.startsWith("CFLAGS=") && gmp_root.nonEmpty) {
            val root0 = gmp_root.get.absolute
            val root1 = platform_context.standard_path(root0)
            require(root0.implode == File.bash_path(root0), "Bad directory name " + root0)
            opt + " " + "-I" + root1 + "/include -L" + root1 + "/lib"
          }
          else opt
        }

      val options3 = if (arch_64) Nil else List("--enable-compact32bit")

      List("--disable-shared", "--enable-intinf-as-int") :::
        options1 ::: options2 ::: options ::: options3
    }

    platform_context.bash(root,
      info.setup + "\n" +
      """
        [ -f Makefile ] && make distclean
        {
          ./configure --prefix="$PWD/target" """ + Bash.strings(configure_options) + """
          rm -rf target
          make && make install
        } || { echo "Build failed" >&2; exit 2; }
      """, redirect = true).check


    /* sha1 library */

    val sha1_files =
      if (sha1_root.isDefined) {
        val dir1 = sha1_root.get
        platform_context.bash(dir1, "./build " + platform_context.sha1, redirect = true).check

        val dir2 = dir1 + Path.explode(platform_context.sha1)
        File.read_dir(dir2).map(entry => dir2 + Path.basic(entry))
      }
      else Nil


    /* install */

    val platform_path = Path.explode(platform_context.polyml(arch_64))

    val platform_dir = target_dir + platform_path
    Isabelle_System.rm_tree(platform_dir)
    Isabelle_System.make_directory(platform_dir)

    val root_platform_dir = Isabelle_System.make_directory(root + platform_path)
    for {
      d <- List("target/bin", "target/lib")
      dir = root + Path.explode(d)
      entry <- File.read_dir(dir)
    } Isabelle_System.move_file(dir + Path.explode(entry), root_platform_dir)

    Isabelle_System.copy_dir(root_platform_dir, platform_dir, direct = true)
    for (file <- sha1_files) Isabelle_System.copy_file(file, platform_dir)

    Executable.libraries_closure(
      platform_dir + Path.basic("poly").platform_exe, mingw = platform_context.mingw,
      filter = info.libs)


    /* polyc: directory prefix */

    val Header = "#! */bin/sh".r
    File.change_lines(platform_dir + Path.explode("polyc")) {
      case Header() :: lines =>
        val lines1 =
          lines.map(line =>
            if (line.startsWith("prefix=")) "prefix=\"$(cd \"$(dirname \"$0\")\"; pwd)\""
            else if (line.startsWith("BINDIR=")) "BINDIR=\"$prefix\""
            else if (line.startsWith("LIBDIR=")) "LIBDIR=\"$prefix\""
            else line)
        "#!/usr/bin/env bash" :: lines1
      case lines =>
        error(cat_lines("Cannot patch polyc -- undetected header:" :: lines.take(3)))
    }
  }



  /** skeleton for component **/

  val standard_gmp_url = "https://gmplib.org/download/gmp/gmp-6.3.0.tar.bz2"

  val default_polyml_url = "https://github.com/polyml/polyml/archive"
  val default_polyml_version = "90c0dbb2514e"
  val default_polyml_name = "polyml-5.9.1"

  val default_sha1_url = "https://isabelle.sketis.net/repos/sha1/archive"
  val default_sha1_version = "0ce12663fe76"

  private def init_src_root(src_dir: Path, input: String, output: String): Unit = {
    val lines = split_lines(File.read(src_dir + Path.explode(input)))
    val ml_files =
      for {
        line <- lines
        rest <- Library.try_unprefix("use", line)
      } yield "ML_file" + rest

    File.write(src_dir + Path.explode(output),
"""(* Poly/ML Compiler root file.

When this file is open in the Prover IDE, the ML files of the Poly/ML
compiler can be explored interactively. This is a separate copy: it does
not affect the running ML session. *)
""" + ml_files.mkString("\n", "\n", "\n"))
  }


  def build_polyml(
    platform_context: Platform_Context,
    options: List[String] = Nil,
    component_name: String = "",
    gmp_url: String = "",
    polyml_url: String = default_polyml_url,
    polyml_version: String = default_polyml_version,
    polyml_name: String = default_polyml_name,
    sha1_url: String = default_sha1_url,
    sha1_version: String = default_sha1_version,
    target_dir: Path = Path.current
  ): Unit = {
    val platform = platform_context.platform
    val progress = platform_context.progress


    /* component */

    val component_name1 = if (component_name.isEmpty) "polyml-" + polyml_version else component_name
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name1)).create(progress = progress)


    /* download and build */

    Isabelle_System.with_tmp_dir("download") { download_dir =>
      /* GMP library */

      val gmp_root: Option[Path] =
        if (gmp_url.isEmpty) None
        else if (platform.is_windows) error("Bad GMP source for Windows: use MinGW version instead")
        else {
          val gmp_dir = Isabelle_System.make_directory(download_dir + Path.basic("gmp"))

          val archive_name =
            Url.get_base_name(gmp_url).getOrElse(error("No base name in " + quote(gmp_url)))
          val archive = download_dir + Path.basic(archive_name)
          Isabelle_System.download_file(gmp_url, archive, progress = progress)
          Isabelle_System.extract(archive, gmp_dir, strip = true)

          val platform_arch = if (platform.is_arm) "aarch64" else "x86_64"
          val platform_os =
            if (platform.is_linux) "unknown-linux-gnu"
            else if (platform.is_windows) "w64-mingw32"
            else if (platform.is_macos) """apple-darwin"$(uname -r)""""
            else error("Bad platform " + platform)

          progress.echo("Building GMP library ...")
          platform_context.bash(gmp_dir,
            script = Library.make_lines(
              "set -e",
              "./configure --enable-cxx --build=" + platform_arch + "-" + platform_os +
                """ --prefix="$PWD/target"""",
              "make",
              "make check",
              "make install"
            )).check

          Some(gmp_dir + Path.explode("target"))
        }


      /* Poly/ML */

      val List(polyml_download, sha1_download) =
        for {
          (url, version, target) <-
            List((polyml_url, polyml_version, "src"), (sha1_url, sha1_version, "sha1"))
        } yield {
          val remote = Url.append_path(url, version + ".tar.gz")
          val download = download_dir + Path.basic(version)
          Isabelle_System.download_file(remote, download.tar.gz, progress = progress)
          Isabelle_System.extract(download.tar.gz, download, strip = true)
          Isabelle_System.extract(
            download.tar.gz, component_dir.path + Path.basic(target), strip = true)
          download
        }

      init_src_root(component_dir.src, "RootArm64.ML", "ROOT0.ML")
      init_src_root(component_dir.src, "RootX86.ML", "ROOT.ML")

      for (arch_64 <- List(false, true)) {
        progress.echo("Building " + platform_context.polyml(arch_64))
        make_polyml(
          platform_context,
          root = polyml_download,
          gmp_root = gmp_root,
          sha1_root = Some(sha1_download),
          target_dir = component_dir.path,
          arch_64 = arch_64,
          options = options)
      }
    }


    /* settings */

    component_dir.write_settings("""# -*- shell-script -*- :mode=shellscript:

POLYML_HOME="$COMPONENT"

if [ -n "$ISABELLE_APPLE_PLATFORM64" ]
then
  if grep "ML_system_apple.*=.*false" "$ISABELLE_HOME_USER/etc/preferences" >/dev/null 2>/dev/null
  then
    ML_PLATFORM="$ISABELLE_PLATFORM64"
  else
    ML_PLATFORM="$ISABELLE_APPLE_PLATFORM64"
  fi
else
  ML_PLATFORM="${ISABELLE_WINDOWS_PLATFORM64:-$ISABELLE_PLATFORM64}"
fi

if grep "ML_system_64.*=.*true" "$ISABELLE_HOME_USER/etc/preferences" >/dev/null 2>/dev/null
then
  ML_OPTIONS="--minheap 1000"
else
  ML_PLATFORM="${ML_PLATFORM/64/64_32}"
  ML_OPTIONS="--minheap 500"
fi

ML_SYSTEM=""" + Bash.string(polyml_name) + """
ML_HOME="$POLYML_HOME/$ML_PLATFORM"
ML_SOURCES="$POLYML_HOME/src"

case "$ML_PLATFORM" in
  *arm64*)
    ISABELLE_DOCS_EXAMPLES="$ISABELLE_DOCS_EXAMPLES:\$ML_SOURCES/ROOT0.ML"
    ;;
  *)
    ISABELLE_DOCS_EXAMPLES="$ISABELLE_DOCS_EXAMPLES:\$ML_SOURCES/ROOT.ML"
    ;;
esac
""")


    /* README */

    File.write(component_dir.README,
"""Poly/ML for Isabelle
====================

This compilation of Poly/ML (https://www.polyml.org) is based on the
source distribution from
https://github.com/polyml/polyml/commit/""" + polyml_version + """

This coincides with the official release of Poly/ML 5.9.1, see also
https://github.com/polyml/polyml/releases/tag/v5.9.1

The Isabelle repository provides an administrative tool "isabelle
component_polyml", which can be used in the polyml component directory as
follows:

* Linux and macOS

  $ isabelle component_polyml -G:

* Windows (Cygwin shell)

  $ isabelle component_polyml -G: -M /cygdrive/c/msys64


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }



  /** Isabelle tool wrappers **/

  val isabelle_tool1 =
    Isabelle_Tool("make_polyml", "make Poly/ML from existing sources", Scala_Project.here,
      { args =>
        var gmp_root: Option[Path] = None
        var mingw = MinGW.none
        var arch_64 = false
        var sha1_root: Option[Path] = None

        val getopts = Getopts("""
Usage: isabelle make_polyml [OPTIONS] ROOT [CONFIGURE_OPTIONS]

  Options are:
    -G DIR       GMP library root
    -M DIR       msys/mingw root specification for Windows
    -m ARCH      processor architecture (32 or 64, default: """ +
        (if (arch_64) "64" else "32") + """)
    -s DIR       sha1 sources, see https://isabelle.sketis.net/repos/sha1

  Make Poly/ML in the ROOT directory of its sources, with additional
  CONFIGURE_OPTIONS.
""",
          "G:" -> (arg => gmp_root = Some(Path.explode(arg))),
          "M:" -> (arg => mingw = MinGW(Path.explode(arg))),
          "m:" ->
            {
              case "32" => arch_64 = false
              case "64" => arch_64 = true
              case bad => error("Bad processor architecture: " + quote(bad))
            },
          "s:" -> (arg => sha1_root = Some(Path.explode(arg))))

        val more_args = getopts(args)
        val (root, options) =
          more_args match {
            case root :: options => (Path.explode(root), options)
            case Nil => getopts.usage()
          }
        make_polyml(Platform_Context(mingw = mingw, progress = new Console_Progress),
          root, gmp_root = gmp_root, sha1_root = sha1_root, arch_64 = arch_64, options = options)
      })

  val isabelle_tool2 =
    Isabelle_Tool("component_polyml", "build Poly/ML component from official repository",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var gmp_url = ""
        var mingw = MinGW.none
        var component_name = ""
        var sha1_url = default_sha1_url
        var sha1_version = default_sha1_version
        var polyml_url = default_polyml_url
        var polyml_version = default_polyml_version
        var polyml_name = default_polyml_name
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_polyml [OPTIONS] [CONFIGURE_OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -G URL       build GMP library from source: explicit URL or ":" for
                 """ + standard_gmp_url + """
    -M DIR       msys/mingw root specification for Windows
    -N NAME      component name (default: derived from Poly/ML version)
    -S URL       SHA1 repository archive area
                 (default: """ + quote(default_sha1_url) + """)
    -T VERSION   SHA1 version (default: """ + quote(default_sha1_version) + """)
    -U URL       Poly/ML repository archive area
                 (default: """ + quote(default_polyml_url) + """)
    -V VERSION   Poly/ML version (default: """ + quote(default_polyml_version) + """)
    -W NAME      Poly/ML name (default: """ + quote(default_polyml_name) + """)
    -v           verbose

  Download and build Poly/ML component from source repositories, with additional
  CONFIGURE_OPTIONS.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "G:" -> (arg => gmp_url = if (arg == ":") standard_gmp_url else arg),
          "M:" -> (arg => mingw = MinGW(Path.explode(arg))),
          "N:" -> (arg => component_name = arg),
          "S:" -> (arg => sha1_url = arg),
          "T:" -> (arg => sha1_version = arg),
          "U:" -> (arg => polyml_url = arg),
          "V:" -> (arg => polyml_version = arg),
          "W:" -> (arg => polyml_name = arg),
          "v" -> (_ => verbose = true))

        val options = getopts(args)

        val progress = new Console_Progress(verbose = verbose)
        val platform_context = Platform_Context(mingw = mingw, progress = progress)

        build_polyml(platform_context, options = options, component_name = component_name,
          gmp_url = gmp_url, polyml_url = polyml_url, polyml_version = polyml_version,
          polyml_name = polyml_name, sha1_url = sha1_url, sha1_version = sha1_version,
          target_dir = target_dir)
      })
}
