/*  Title:      Pure/Admin/build_polyml.scala
    Author:     Makarius

Build Poly/ML from sources.
*/

package isabelle


import scala.util.matching.Regex


object Build_PolyML
{
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
        options =
          List("--build=x86_64-darwin", "CFLAGS=-arch x86_64 -O3 -I../libffi/include",
            "CXXFLAGS=-arch x86_64 -O3 -I../libffi/include", "CCASFLAGS=-arch x86_64",
            "LDFLAGS=-segprot POLY rwx rwx"),
        setup = "PATH=/usr/bin:/bin:/usr/sbin:/sbin",
        libs = Set("libpolyml", "libgmp")),
    "windows" ->
      Platform_Info(
        options =
          List("--host=x86_64-w64-mingw32", "CPPFLAGS=-I/mingw64/include", "--disable-windows-gui"),
        setup = MinGW.environment_export,
        libs = Set("libgcc_s_seh", "libgmp", "libstdc++", "libwinpthread")))

  def build_polyml(
    root: Path,
    sha1_root: Option[Path] = None,
    progress: Progress = new Progress,
    arch_64: Boolean = false,
    options: List[String] = Nil,
    mingw: MinGW = MinGW.none)
  {
    if (!((root + Path.explode("configure")).is_file && (root + Path.explode("PolyML")).is_dir))
      error("Bad Poly/ML root directory: " + root)

    val platform = Isabelle_Platform.self
    val platform_arch =
      if (arch_64) platform.arch_64
      else if (platform.is_intel) "x86_64_32"
      else platform.arch_32

    val polyml_platform = platform_arch + "-" + platform.os_name
    val sha1_platform = platform.arch_64 + "-" + platform.os_name

    val info =
      platform_info.getOrElse(platform.os_name,
        error("Bad OS platform: " + quote(platform.os_name)))

    if (platform.is_linux) Isabelle_System.require_command("chrpath")


    /* bash */

    def bash(
      cwd: Path, script: String, redirect: Boolean = false, echo: Boolean = false): Process_Result =
    {
      progress.bash(mingw.bash_script(script), cwd = cwd.file, redirect = redirect, echo = echo)
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
          make compiler && make compiler && make install
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

    val platform_dir = Path.explode(polyml_platform)
    Isabelle_System.rm_tree(platform_dir)
    Isabelle_System.make_directory(platform_dir)

    for (file <- sha1_files) File.copy(file, platform_dir)

    for {
      d <- List("target/bin", "target/lib")
      dir = root + Path.explode(d)
      entry <- File.read_dir(dir)
    } File.move(dir + Path.explode(entry), platform_dir)

    Executable.libraries_closure(
      platform_dir + Path.basic("poly").platform_exe, mingw = mingw, filter = info.libs)


    /* polyc: directory prefix */

    val Header = "#! */bin/sh".r
    File.change(platform_dir + Path.explode("polyc"), txt =>
      split_lines(txt) match {
        case Header() :: lines =>
          val lines1 =
            lines.map(line =>
              if (line.startsWith("prefix=")) "prefix=\"$(cd \"$(dirname \"$0\")\"; pwd)\""
              else if (line.startsWith("BINDIR=")) "BINDIR=\"$prefix\""
              else if (line.startsWith("LIBDIR=")) "LIBDIR=\"$prefix\""
              else line)
          cat_lines("#!/usr/bin/env bash" ::lines1)
        case lines =>
          error(cat_lines("Cannot patch polyc -- undetected header:" :: lines.take(3)))
      }
    )
  }



  /** skeleton for component **/

  private def extract_sources(source_archive: Path, component_dir: Path) =
  {
    if (source_archive.get_ext == "zip") {
      Isabelle_System.bash(
        "unzip -x " + File.bash_path(source_archive.absolute), cwd = component_dir.file).check
    }
    else {
      Isabelle_System.gnutar("-xzf " + File.bash_path(source_archive), dir = component_dir).check
    }

    val src_dir = component_dir + Path.explode("src")
    File.read_dir(component_dir) match {
      case List(s) => File.move(component_dir + Path.basic(s), src_dir)
      case _ => error("Source archive contains multiple directories")
    }

    val lines = split_lines(File.read(src_dir + Path.explode("RootX86.ML")))
    val ml_files =
      for {
        line <- lines
        rest <- Library.try_unprefix("use", line)
      } yield "ML_file" + rest

    File.write(src_dir + Path.explode("ROOT.ML"),
"""(* Poly/ML Compiler root file.

When this file is open in the Prover IDE, the ML files of the Poly/ML
compiler can be explored interactively. This is a separate copy: it does
not affect the running ML session. *)
""" + ml_files.mkString("\n", "\n", "\n"))
  }

  def build_polyml_component(
    source_archive: Path,
    component_dir: Path,
    sha1_root: Option[Path] = None)
  {
    Isabelle_System.new_directory(component_dir)
    extract_sources(source_archive, component_dir)

    File.copy(Path.explode("~~/Admin/polyml/README"), component_dir)

    val etc_dir = Isabelle_System.make_directory(component_dir + Path.explode("etc"))
    File.copy(Path.explode("~~/Admin/polyml/settings"), etc_dir)

    sha1_root match {
      case Some(dir) =>
        Mercurial.repository(dir).archive(File.standard_path(component_dir + Path.explode("sha1")))
      case None =>
    }
  }



  /** Isabelle tool wrappers **/

  val isabelle_tool1 =
    Isabelle_Tool("build_polyml", "build Poly/ML from sources", args =>
    {
      var mingw = MinGW.none
      var arch_64 = Isabelle_Platform.self.is_arm
      var sha1_root: Option[Path] = None

      val getopts = Getopts("""
Usage: isabelle build_polyml [OPTIONS] ROOT [CONFIGURE_OPTIONS]

  Options are:
    -M DIR       msys/mingw root specification for Windows
    -m ARCH      processor architecture (32 or 64, default: """ +
        (if (arch_64) "64" else "32") + """)
    -s DIR       sha1 sources, see https://isabelle.sketis.net/repos/sha1

  Build Poly/ML in the ROOT directory of its sources, with additional
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
      build_polyml(root, sha1_root = sha1_root, progress = new Console_Progress,
        arch_64 = arch_64, options = options, mingw = mingw)
    })

  val isabelle_tool2 =
    Isabelle_Tool("build_polyml_component", "make skeleton for Poly/ML component", args =>
    {
      var sha1_root: Option[Path] = None

      val getopts = Getopts("""
Usage: isabelle build_polyml_component [OPTIONS] SOURCE_ARCHIVE COMPONENT_DIR

  Options are:
    -s DIR       sha1 sources, see https://isabelle.sketis.net/repos/sha1

  Make skeleton for Poly/ML component, based on official source archive
  (zip or tar.gz).
""",
        "s:" -> (arg => sha1_root = Some(Path.explode(arg))))

      val more_args = getopts(args)

      val (source_archive, component_dir) =
        more_args match {
          case List(archive, dir) => (Path.explode(archive), Path.explode(dir))
          case _ => getopts.usage()
        }
      build_polyml_component(source_archive, component_dir, sha1_root = sha1_root)
    })
}
