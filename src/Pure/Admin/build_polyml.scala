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
    copy_files: List[String] = Nil,
    ldd_pattern: Option[(String, Regex)] = None)

  private val platform_info = Map(
    "linux" ->
      Platform_Info(
        options = List("LDFLAGS=-Wl,-rpath,_DUMMY_"),
        ldd_pattern = Some(("ldd", """\s*libgmp.*=>\s*(\S+).*""".r))),
    "darwin" ->
      Platform_Info(
        options =
          List("--build=x86_64-darwin", "CFLAGS=-arch x86_64 -O3 -I../libffi/include",
            "CXXFLAGS=-arch x86_64 -O3 -I../libffi/include", "CCASFLAGS=-arch x86_64",
            "LDFLAGS=-segprot POLY rwx rwx"),
        setup = "PATH=/usr/bin:/bin:/usr/sbin:/sbin",
        ldd_pattern = Some(("otool -L", """\s*(\S+lib(?:polyml|gmp).*dylib).*""".r))),
    "windows" ->
      Platform_Info(
        options =
          List("--host=x86_64-w64-mingw32", "CPPFLAGS=-I/mingw64/include", "--disable-windows-gui"),
        setup =
          """PATH=/usr/bin:/bin:/mingw64/bin
            export CONFIG_SITE=/etc/config.site""",
        copy_files =
          List("$MSYS/mingw64/bin/libgcc_s_seh-1.dll",
            "$MSYS/mingw64/bin/libgmp-10.dll",
            "$MSYS/mingw64/bin/libstdc++-6.dll")))

  def build_polyml(
    root: Path,
    sha1_root: Option[Path] = None,
    progress: Progress = No_Progress,
    arch_64: Boolean = false,
    options: List[String] = Nil,
    msys_root: Option[Path] = None)
  {
    if (!((root + Path.explode("configure")).is_file && (root + Path.explode("PolyML")).is_dir))
      error("Bad Poly/ML root directory: " + root)

    val platform_arch = if (arch_64) "x86_64" else "x86_64_32"
    val platform_os = Platform.os_name

    val platform = platform_arch + "-" + platform_os
    val platform_64 = "x86_64-" + platform_os

    val info =
      platform_info.get(platform_os) getOrElse
        error("Bad OS platform: " + quote(platform_os))

    val settings =
      msys_root match {
        case None if Platform.is_windows =>
          error("Windows requires specification of msys root directory")
        case None => Isabelle_System.settings()
        case Some(msys) => Isabelle_System.settings() + ("MSYS" -> msys.expand.implode)
      }


    /* bash */

    def bash(
      cwd: Path, script: String, redirect: Boolean = false, echo: Boolean = false): Process_Result =
    {
      val script1 =
        msys_root match {
          case None => script
          case Some(msys) =>
            File.bash_path(msys + Path.explode("usr/bin/bash")) + " -c " + Bash.string(script)
        }
      progress.bash(script1, cwd = cwd.file, redirect = redirect, echo = echo)
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

    val ldd_files =
    {
      info.ldd_pattern match {
        case Some((ldd, pattern)) =>
          val lines = bash(root, ldd + " target/bin/poly").check.out_lines
          for { line <- lines; List(lib) <- pattern.unapplySeq(line) } yield lib
        case None => Nil
      }
    }


    /* sha1 library */

    val sha1_files =
      if (sha1_root.isDefined) {
        val dir1 = sha1_root.get
        bash(dir1, "./build " + platform_64, redirect = true, echo = true).check

        val dir2 = dir1 + Path.explode(platform_64)
        File.read_dir(dir2).map(entry => dir2.implode + "/" + entry)
      }
      else Nil


    /* target */

    val target = Path.explode(platform)
    Isabelle_System.rm_tree(target)
    Isabelle_System.mkdirs(target)

    for (file <- info.copy_files ::: ldd_files ::: sha1_files)
      File.copy(Path.explode(file).expand_env(settings), target)

    for {
      d <- List("target/bin", "target/lib")
      dir = root + Path.explode(d)
      entry <- File.read_dir(dir)
    } File.move(dir + Path.explode(entry), target)


    /* poly: library path */

    if (Platform.is_linux) {
      bash(target, "chrpath -r '$ORIGIN' poly", echo = true).check
    }
    else if (Platform.is_macos) {
      for (file <- ldd_files) {
        bash(target,
          """install_name_tool -change """ + Bash.string(file) + " " +
            Bash.string("@executable_path/" + Path.explode(file).file_name) + " poly").check
      }
    }


    /* polyc: directory prefix */

    {
      val polyc_path = target + Path.explode("polyc")

      val Header = "#! */bin/sh".r
      val polyc_patched =
        split_lines(File.read(polyc_path)) match {
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
      File.write(polyc_path, polyc_patched)
    }
  }



  /** skeleton for component **/

  def build_polyml_component(component: Path, sha1_root: Option[Path] = None)
  {
    if (component.is_dir) error("Directory already exists: " + component)

    val etc = component + Path.explode("etc")
    Isabelle_System.mkdirs(etc)
    File.copy(Path.explode("~~/Admin/polyml/settings"), etc)
    File.copy(Path.explode("~~/Admin/polyml/README"), component)

    sha1_root match {
      case Some(dir) =>
        Mercurial.repository(dir).archive(File.standard_path(component + Path.explode("sha1")))
      case None =>
    }
  }



  /** Isabelle tool wrappers **/

  val isabelle_tool1 =
    Isabelle_Tool("build_polyml", "build Poly/ML from sources", args =>
    {
      Command_Line.tool0 {
        var msys_root: Option[Path] = None
        var arch_64 = false
        var sha1_root: Option[Path] = None

        val getopts = Getopts("""
Usage: isabelle build_polyml [OPTIONS] ROOT [CONFIGURE_OPTIONS]

  Options are:
    -M DIR       msys root directory (for Windows)
    -m ARCH      processor architecture (32=x86_64_32, 64=x86_64, default: 32)
    -s DIR       sha1 sources, see https://isabelle.sketis.net/repos/sha1

  Build Poly/ML in the ROOT directory of its sources, with additional
  CONFIGURE_OPTIONS (e.g. --without-gmp).
""",
          "M:" -> (arg => msys_root = Some(Path.explode(arg))),
          "m:" ->
            {
              case "32" | "x86_64_32" => arch_64 = false
              case "64" | "x86_64" => arch_64 = true
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
          arch_64 = arch_64, options = options, msys_root = msys_root)
      }
    })

  val isabelle_tool2 =
    Isabelle_Tool("build_polyml_component", "make skeleton for Poly/ML component", args =>
    {
      Command_Line.tool0 {
        var sha1_root: Option[Path] = None

        val getopts = Getopts("""
Usage: isabelle build_polyml_component [OPTIONS] TARGET

  Options are:
    -s DIR       sha1 sources, see https://isabelle.sketis.net/repos/sha1

  Make skeleton for Poly/ML component in directory TARGET.
""",
          "s:" -> (arg => sha1_root = Some(Path.explode(arg))))

        val more_args = getopts(args)
        val component =
          more_args match {
            case List(arg) => Path.explode(arg)
            case _ => getopts.usage()
          }
        build_polyml_component(component, sha1_root = sha1_root)
      }
    })
}
