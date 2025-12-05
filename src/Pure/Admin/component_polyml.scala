/*  Title:      Pure/Admin/component_polyml.scala
    Author:     Makarius

Build Poly/ML from sources.

Note: macOS 14 Sonoma requires "LDFLAGS=... -ld64".
*/

package isabelle


object Component_PolyML {
  /** platform information **/

  object Platform_Info {
    def apply(platform: Isabelle_Platform): Platform_Info =
      if (platform.is_linux) {
        Platform_Info(
          platform = platform,
          options = List("LDFLAGS=-Wl,-rpath,_DUMMY_"),
          libs = Set("libgmp"))
      }
      else if (platform.is_macos) {
        Platform_Info(
          platform = platform,
          options = List("CFLAGS=-O3", "CXXFLAGS=-O3", "LDFLAGS=-segprot POLY rwx rwx"),
          setup = "PATH=/usr/bin:/bin:/usr/sbin:/sbin",
          libs = Set("libpolyml", "libgmp"))
      }
      else if (platform.is_windows) {
        Platform_Info(
          platform = platform,
          options =
            List("--host=x86_64-w64-mingw32", "CPPFLAGS=-I/mingw64/include", "--disable-windows-gui"),
          setup = MinGW.env_prefix,
          libs = Set("libgcc_s_seh", "libgmp", "libstdc++", "libwinpthread"))
      }
      else error("Bad platform: " + quote(platform.toString))
  }

  sealed case class Platform_Info(
    platform: Isabelle_Platform = Isabelle_Platform.local,
    options: List[String] = Nil,
    setup: String = "",
    libs: Set[String] = Set.empty
  ) {
    def polyml(arch_64: Boolean): String =
      (if (arch_64) platform.arch_64 else platform.arch_64_32) + "-" + platform.os_name
  }


  /** build stages **/

  def make_polyml_gmp(
    platform_context: Isabelle_Platform.Context,
    dir: Path,
    options: List[String] = Nil
  ): Path = {
    val progress = platform_context.progress
    val platform = platform_context.isabelle_platform

    val platform_arch = if (platform.is_arm) "aarch64" else "x86_64"
    val platform_os =
      if (platform.is_linux) "unknown-linux-gnu"
      else if (platform.is_windows) "w64-mingw32"
      else if (platform.is_macos) """apple-darwin"$(uname -r)""""
      else error("Bad platform " + platform)

    val root = dir.absolute
    val target_dir = root + Path.explode("target")

    progress.echo("Building GMP library ...")
    platform_context.bash(
      Library.make_lines(
        "set -e",
        "[ -f Makefile ] && make distclean",
        "./configure --disable-static --enable-shared --enable-cxx" +
          " --build=" + platform_arch + "-" + platform_os +
          """ --prefix="$PWD/target" """ + Bash.strings(options),
        "rm -rf target",
        "make",
        "make check",
        "make install"), cwd = root).check

    if (platform.is_windows) {
      val bin_dir = target_dir + Path.explode("bin")
      val lib_dir = target_dir + Path.explode("lib")
      Isabelle_System.copy_dir(bin_dir, lib_dir, direct = true)
    }

    target_dir
  }

  def make_polyml(
    platform_context: Isabelle_Platform.Context,
    root: Path,
    gmp_root: Option[Path] = None,
    sha1_root: Option[Path] = None,
    target_dir: Path = Path.current,
    arch_64: Boolean = false,
    options: List[String] = Nil
  ): Unit = {
    if (!((root + Path.explode("configure")).is_file && (root + Path.explode("PolyML")).is_dir))
      error("Bad Poly/ML root directory: " + root)

    val platform = platform_context.isabelle_platform
    val platform_info = Platform_Info(platform)


    /* configure and make */

    val configure_options = {
      val options1 =
        if (gmp_root.nonEmpty) List("--with-gmp") else List("--without-gmp")

      def detect_CFLAGS(s: String): Boolean = s.startsWith("CFLAGS=")

      val info_options =
        if (platform_info.options.exists(detect_CFLAGS)) platform_info.options
        else "CFLAGS=" :: platform_info.options

      val options2 =
        for (opt <- info_options) yield {
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

    val gmp_setup =
      gmp_root match {
        case Some(dir) =>
          val v = Executable.library_path_variable(platform)
          val s = platform_context.standard_path(dir.absolute) + "/lib"
          "export " + v + "=" + quote(s + ":" + "$" + v)
        case None => ""
      }

    platform_context.bash(
      Library.make_lines(
        "set -e",
        platform_info.setup,
        gmp_setup,
        "[ -f Makefile ] && make distclean",
        """./configure --prefix="$PWD/target" """ + Bash.strings(configure_options),
        "rm -rf target",
        "make",
        "make install"), cwd = root).check


    /* sha1 library */

    val sha1_files =
      sha1_root match {
        case Some(dir) =>
          val platform_path = Path.explode(platform.ISABELLE_PLATFORM(windows = true, apple = true))
          val platform_dir = dir + platform_path
          platform_context.bash("./build " + File.bash_path(platform_path), cwd = dir).check
          File.read_dir(platform_dir).map(entry => platform_dir + Path.basic(entry))
        case None => Nil
      }


    /* install */

    val platform_path = Path.explode(platform_info.polyml(arch_64))
    val platform_dir = target_dir + platform_path

    Isabelle_System.rm_tree(platform_dir)
    Isabelle_System.make_directory(platform_dir)

    for (d <- List("target/bin", "target/lib")) {
      Isabelle_System.copy_dir(root + Path.explode(d), platform_dir, direct = true)
    }

    for (file <- sha1_files) Isabelle_System.copy_file(file, platform_dir)

    Executable.library_closure(
      platform_dir + Path.basic("poly").platform_exe,
      env_prefix = gmp_setup + "\n",
      mingw = platform_context.mingw,
      filter = platform_info.libs)


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

  val default_gmp_url = "https://gmplib.org/download/gmp/gmp-6.3.0.tar.bz2"

  val default_polyml_url = "https://github.com/polyml/polyml/archive"
  val default_polyml_version = "455755407707"
  val default_polyml_name = "polyml-5.9.2"

  val default_sha1_url = "https://files.sketis.net/sha1/archive"
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
    platform_context: Isabelle_Platform.Context,
    options: List[String] = Nil,
    component_name: String = "",
    gmp_url: String = "",
    gmp_root: Option[Path] = None,
    polyml_url: String = default_polyml_url,
    polyml_version: String = default_polyml_version,
    polyml_name: String = default_polyml_name,
    sha1_url: String = default_sha1_url,
    sha1_version: String = default_sha1_version,
    target_dir: Path = Path.current
  ): Unit = {
    val platform = platform_context.isabelle_platform
    val platform_info = Platform_Info(platform)

    val progress = platform_context.progress


    /* component */

    val component_name1 = if (component_name.isEmpty) "polyml-" + polyml_version else component_name
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name1)).create(progress = progress)


    /* download and build */

    Isabelle_System.with_tmp_dir("build") { build_dir =>
      /* GMP library */

      val gmp_root1: Option[Path] =
        if (gmp_url.isEmpty) gmp_root
        else {
          val gmp_dir = Isabelle_System.make_directory(build_dir + Path.basic("gmp"))

          val archive_name =
            Url.get_base_name(gmp_url).getOrElse(error("No base name in " + quote(gmp_url)))
          val archive = build_dir + Path.basic(archive_name)
          Isabelle_System.download_file(gmp_url, archive, progress = progress)
          Isabelle_System.extract(archive, gmp_dir, strip = true)

          Some(make_polyml_gmp(platform_context, gmp_dir))
        }


      /* Poly/ML */

      val List(polyml_download, sha1_download) =
        for {
          (url, version, target) <-
            List((polyml_url, polyml_version, "src"), (sha1_url, sha1_version, "sha1"))
        } yield {
          val remote = Url.append_path(url, version + ".tar.gz")
          val download = build_dir + Path.basic(version)
          Isabelle_System.download_file(remote, download.tar.gz, progress = progress)
          Isabelle_System.extract(download.tar.gz, download, strip = true)
          Isabelle_System.extract(
            download.tar.gz, component_dir.path + Path.basic(target), strip = true)
          download
        }

      init_src_root(component_dir.src, "RootArm64.ML", "ROOT0.ML")
      init_src_root(component_dir.src, "RootX86.ML", "ROOT.ML")

      for (arch_64 <- List(false, true)) {
        progress.echo("Building Poly/ML " + platform_info.polyml(arch_64))
        make_polyml(
          platform_context,
          root = polyml_download,
          gmp_root = gmp_root1,
          sha1_root = Some(sha1_download),
          target_dir = component_dir.path,
          arch_64 = arch_64,
          options = options)
      }
    }


    /* settings */

    component_dir.write_settings("""
POLYML_HOME="$COMPONENT"

ML_SYSTEM=""" + Bash.string(polyml_name) + """
ML_OPTIONS32="--minheap 500"
ML_OPTIONS64="--minheap 1000"
ML_OPTIONS=""
ML_PLATFORM=""

ISABELLE_DOCS_EXAMPLES="$ISABELLE_DOCS_EXAMPLES:\$POLYML_HOME/\$ML_SOURCES_ROOT"
""")


    /* README */

    File.write(component_dir.README,
"""Poly/ML for Isabelle
====================

This compilation of Poly/ML (https://www.polyml.org) is based on the
source distribution from
https://github.com/polyml/polyml/commit/""" + polyml_version + """

This coincides with the official release of Poly/ML 5.9.2, see also
https://github.com/polyml/polyml/releases/tag/v5.9.2

The Isabelle repository provides an administrative tool "isabelle
component_polyml", which can be used in the polyml component directory as
follows:

* Linux and macOS

  $ isabelle component_polyml

* Windows (Cygwin shell)

  $ isabelle component_polyml -M /cygdrive/c/msys64


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }



  /** Isabelle tool wrappers **/

  val isabelle_tool1 =
    Isabelle_Tool("make_polyml_gmp", "make GMP library from existing sources", Scala_Project.here,
      { args =>
        var mingw = MinGW.none
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle make_polyml_gmp [OPTIONS] ROOT [CONFIGURE_OPTIONS]

  Options are:
    -M DIR       msys/mingw root specification for Windows

  Make GMP library in the ROOT directory of its sources, with additional
  CONFIGURE_OPTIONS.
""",
          "M:" -> (arg => mingw = MinGW(Path.explode(arg))),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        val (root, options) =
          more_args match {
            case root :: options => (Path.explode(root), options)
            case Nil => getopts.usage()
          }

        val progress = new Console_Progress(verbose = verbose)

        val platform_context = Isabelle_Platform.Context(mingw = mingw, progress = progress)
        val target_dir = make_polyml_gmp(platform_context, root, options = options)

        progress.echo("GMP installation directory: " + target_dir)
      })

  val isabelle_tool2 =
    Isabelle_Tool("make_polyml", "make Poly/ML from existing sources", Scala_Project.here,
      { args =>
        var gmp_root: Option[Path] = None
        var mingw = MinGW.none
        var arch_64 = false
        var sha1_root: Option[Path] = None
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle make_polyml [OPTIONS] ROOT [CONFIGURE_OPTIONS]

  Options are:
    -M DIR       msys/mingw root specification for Windows
    -g DIR       GMP library root
    -m ARCH      processor architecture (32 or 64, default: """ +
        (if (arch_64) "64" else "32") + """)
    -s DIR       sha1 sources, see https://isabelle.sketis.net/repos/sha1

  Make Poly/ML in the ROOT directory of its sources, with additional
  CONFIGURE_OPTIONS.
""",
          "M:" -> (arg => mingw = MinGW(Path.explode(arg))),
          "g:" -> (arg => gmp_root = Some(Path.explode(arg))),
          "m:" ->
            {
              case "32" => arch_64 = false
              case "64" => arch_64 = true
              case bad => error("Bad processor architecture: " + quote(bad))
            },
          "s:" -> (arg => sha1_root = Some(Path.explode(arg))),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        val (root, options) =
          more_args match {
            case root :: options => (Path.explode(root), options)
            case Nil => getopts.usage()
          }

        val progress = new Console_Progress(verbose = verbose)
        val platform_context = Isabelle_Platform.Context(mingw = mingw, progress = progress)
        make_polyml(platform_context, root,
          gmp_root = gmp_root, sha1_root = sha1_root, arch_64 = arch_64, options = options)
      })

  val isabelle_tool3 =
    Isabelle_Tool("component_polyml", "build Poly/ML component from official repository",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var gmp_url = default_gmp_url
        var mingw = MinGW.none
        var component_name = ""
        var sha1_url = default_sha1_url
        var sha1_version = default_sha1_version
        var polyml_url = default_polyml_url
        var polyml_version = default_polyml_version
        var polyml_name = default_polyml_name
        var gmp_root: Option[Path] = None
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_polyml [OPTIONS] [CONFIGURE_OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -G URL       build GMP library from source (overrides option -g)
                 (default """ + quote(default_gmp_url) + """)
    -M DIR       msys/mingw root specification for Windows
    -N NAME      component name (default: derived from Poly/ML version)
    -S URL       SHA1 repository archive area
                 (default: """ + quote(default_sha1_url) + """)
    -T VERSION   SHA1 version (default: """ + quote(default_sha1_version) + """)
    -U URL       Poly/ML repository archive area
                 (default: """ + quote(default_polyml_url) + """)
    -V VERSION   Poly/ML version (default: """ + quote(default_polyml_version) + """)
    -W NAME      Poly/ML name (default: """ + quote(default_polyml_name) + """)
    -g DIR       use existing GMP library (overrides option -G)
    -v           verbose

  Download and build Poly/ML component from source repositories, with additional
  CONFIGURE_OPTIONS.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "G:" -> (arg => { gmp_url = arg; gmp_root = None }),
          "M:" -> (arg => mingw = MinGW(Path.explode(arg))),
          "N:" -> (arg => component_name = arg),
          "S:" -> (arg => sha1_url = arg),
          "T:" -> (arg => sha1_version = arg),
          "U:" -> (arg => polyml_url = arg),
          "V:" -> (arg => polyml_version = arg),
          "W:" -> (arg => polyml_name = arg),
          "g:" -> (arg => { gmp_root = Some(Path.explode(arg)); gmp_url = "" }),
          "v" -> (_ => verbose = true))

        val options = getopts(args)

        val progress = new Console_Progress(verbose = verbose)
        val platform_context = Isabelle_Platform.Context(mingw = mingw, progress = progress)

        build_polyml(platform_context, options = options, component_name = component_name,
          gmp_url = gmp_url, gmp_root = gmp_root, polyml_url = polyml_url,
          polyml_version = polyml_version, polyml_name = polyml_name, sha1_url = sha1_url,
          sha1_version = sha1_version, target_dir = target_dir)
      })
}
