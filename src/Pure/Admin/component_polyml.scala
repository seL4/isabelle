/*  Title:      Pure/Admin/component_polyml.scala
    Author:     Makarius

Build Poly/ML from sources.

Note: macOS 14 Sonoma requires "LDFLAGS=... -ld64".
*/

package isabelle


import scala.util.matching.Regex


object Component_PolyML {
  /** platform-specific build **/

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
        setup = MinGW.environment_export,
        libs = Set("libgcc_s_seh", "libgmp", "libstdc++", "libwinpthread")))

  def polyml_platform(arch_64: Boolean): String = {
    val platform = Isabelle_Platform.self
    (if (arch_64) platform.arch_64 else platform.arch_64_32) + "-" + platform.os_name
  }

  def make_polyml(
    root: Path,
    sha1_root: Option[Path] = None,
    target_dir: Path = Path.current,
    arch_64: Boolean = false,
    options: List[String] = Nil,
    mingw: MinGW = MinGW.none,
    progress: Progress = new Progress,
  ): Unit = {
    if (!((root + Path.explode("configure")).is_file && (root + Path.explode("PolyML")).is_dir))
      error("Bad Poly/ML root directory: " + root)

    val platform = Isabelle_Platform.self

    val sha1_platform = platform.arch_64 + "-" + platform.os_name

    val info =
      platform_info.getOrElse(platform.os_name,
        error("Bad OS platform: " + quote(platform.os_name)))

    if (platform.is_linux) Isabelle_System.require_command("patchelf")


    /* bash */

    def bash(
      cwd: Path, script: String,
      redirect: Boolean = false,
      echo: Boolean = false
    ): Process_Result = {
      val script1 =
        if (platform.is_arm && platform.is_macos) {
          "arch -arch arm64 bash -c " + Bash.string(script)
        }
        else mingw.bash_script(script)
      progress.bash(script1, cwd = cwd, redirect = redirect, echo = echo)
    }


    /* configure and make */

    val configure_options =
      List("--disable-shared", "--enable-intinf-as-int", "--with-gmp") :::
        info.options ::: options ::: (if (arch_64) Nil else List("--enable-compact32bit"))

    bash(root,
      info.setup + "\n" +
      """
        [ -f Makefile ] && make distclean
        {
          ./configure --prefix="$PWD/target" """ + Bash.strings(configure_options) + """
          rm -rf target
          make && make install
        } || { echo "Build failed" >&2; exit 2; }
      """, redirect = true, echo = true).check


    /* sha1 library */

    val sha1_files =
      if (sha1_root.isDefined) {
        val dir1 = sha1_root.get
        bash(dir1, "./build " + sha1_platform, redirect = true, echo = true).check

        val dir2 = dir1 + Path.explode(sha1_platform)
        File.read_dir(dir2).map(entry => dir2 + Path.basic(entry))
      }
      else Nil


    /* install */

    val platform_path = Path.explode(polyml_platform(arch_64))

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
      platform_dir + Path.basic("poly").platform_exe, mingw = mingw, filter = info.libs)


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
    options: List[String] = Nil,
    mingw: MinGW = MinGW.none,
    component_name: String = "",
    polyml_url: String = default_polyml_url,
    polyml_version: String = default_polyml_version,
    polyml_name: String = default_polyml_name,
    sha1_url: String = default_sha1_url,
    sha1_version: String = default_sha1_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    /* component */

    val component_name1 = if (component_name.isEmpty) "polyml-" + polyml_version else component_name
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name1)).create(progress = progress)


    /* download and build */

    Isabelle_System.with_tmp_dir("download") { download_dir =>
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
        progress.echo("Building " + polyml_platform(arch_64))
        make_polyml(
          root = polyml_download,
          sha1_root = Some(sha1_download),
          target_dir = component_dir.path,
          arch_64 = arch_64,
          options = options,
          mingw = mingw,
          progress = if (progress.verbose) progress else new Progress)
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

  $ isabelle component_polyml

* Windows (Cygwin shell)

  $ isabelle component_polyml -M /cygdrive/c/msys64


Building libgmp on macOS
========================

The build_polyml invocations above implicitly use the GNU Multiple Precision
Arithmetic Library (libgmp), but that is not available on macOS by default.
Appending "--without-gmp" to the command-line omits this library. Building
libgmp properly from sources works as follows (library headers and binaries
will be placed in /usr/local).

* Download:

  $ curl https://gmplib.org/download/gmp/gmp-6.3.0.tar.bz2 | tar xjf -
  $ cd gmp-6.3.0

* build:

  $ make distclean

  #Intel
  $ ./configure --enable-cxx --build=core2-apple-darwin"$(uname -r)"

  #ARM
  $ ./configure --enable-cxx --build=aarch64-apple-darwin"$(uname -r)"

  $ make && make check
  $ sudo make install


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }



  /** Isabelle tool wrappers **/

  val isabelle_tool1 =
    Isabelle_Tool("make_polyml", "make Poly/ML from existing sources", Scala_Project.here,
      { args =>
        var mingw = MinGW.none
        var arch_64 = false
        var sha1_root: Option[Path] = None

        val getopts = Getopts("""
Usage: isabelle make_polyml [OPTIONS] ROOT [CONFIGURE_OPTIONS]

  Options are:
    -M DIR       msys/mingw root specification for Windows
    -m ARCH      processor architecture (32 or 64, default: """ +
        (if (arch_64) "64" else "32") + """)
    -s DIR       sha1 sources, see https://isabelle.sketis.net/repos/sha1

  Make Poly/ML in the ROOT directory of its sources, with additional
  CONFIGURE_OPTIONS (e.g. --without-gmp).
""",
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
        make_polyml(root, sha1_root = sha1_root, progress = new Console_Progress,
          arch_64 = arch_64, options = options, mingw = mingw)
      })

  val isabelle_tool2 =
    Isabelle_Tool("component_polyml", "build Poly/ML component from official repository",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
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
  CONFIGURE_OPTIONS (e.g. --without-gmp).
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
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

        build_polyml(options = options, mingw = mingw, component_name = component_name,
          polyml_url = polyml_url, polyml_version = polyml_version, polyml_name = polyml_name,
          sha1_url = sha1_url, sha1_version = sha1_version, target_dir = target_dir,
          progress = progress)
      })
}
