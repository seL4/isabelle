/*  Title:      Pure/Admin/build_polyml.scala
    Author:     Makarius

Build Poly/ML from sources.
*/

package isabelle


object Build_PolyML
{
  /** build_polyml **/

  sealed case class Platform_Info(
    options: List[String] = Nil,
    options_multilib: List[String] = Nil,
    setup: String = "",
    copy_files: List[String] = Nil)

  private val platform_info = Map(
    "x86-linux" ->
      Platform_Info(
        options_multilib =
          List("--build=i386", "CFLAGS=-m32 -O3", "CXXFLAGS=-m32 -O3", "CCASFLAGS=-m32")),
    "x86_64-linux" -> Platform_Info(),
    "x86-darwin" ->
      Platform_Info(
        options =
          List("--build=i686-darwin", "CFLAGS=-arch i686 -O3 -I../libffi/include",
            "CXXFLAGS=-arch i686 -O3 -I../libffi/include", "CCASFLAGS=-arch i686 -O3",
            "LDFLAGS=-segprot POLY rwx rwx")),
    "x86_64-darwin" ->
      Platform_Info(
        options =
          List("--build=x86_64-darwin", "CFLAGS=-arch x86_64 -O3 -I../libffi/include",
            "CXXFLAGS=-arch x86_64 -O3 -I../libffi/include", "CCASFLAGS=-arch x86_64",
            "LDFLAGS=-segprot POLY rwx rwx")),
    "x86-windows" ->
      Platform_Info(
        options =
          List("--host=i686-w32-mingw32", "CPPFLAGS=-I/mingw32/include", "--disable-windows-gui"),
        setup =
          """PATH=/usr/bin:/bin:/mingw32/bin
            export CONFIG_SITE=/etc/config.site""",
        copy_files =
          List("/mingw32/bin/libgcc_s_dw2-1.dll",
            "/mingw32/bin/libgmp-10.dll",
            "/mingw32/bin/libstdc++-6.dll")),
    "x86_64-windows" ->
      Platform_Info(
        options =
          List("--host=x86_64-w64-mingw32", "CPPFLAGS=-I/mingw64/include", "--disable-windows-gui"),
        setup =
          """PATH=/usr/bin:/bin:/mingw64/bin
            export CONFIG_SITE=/etc/config.site""",
        copy_files =
          List("/mingw64/bin/libgcc_s_seh-1.dll",
            "/mingw64/bin/libgmp-10.dll",
            "/mingw64/bin/libstdc++-6.dll")))

  def build_polyml(
    root: Path,
    sha1_root: Option[Path] = None,
    progress: Progress = Ignore_Progress,
    arch_64: Boolean = false,
    options: List[String] = Nil,
    other_bash: String = "")
  {
    if (!((root + Path.explode("configure")).is_file && (root + Path.explode("PolyML")).is_dir))
      error("Bad Poly/ML root directory: " + root)

    val platform =
      (if (arch_64) "x86_64" else "x86") +
      (if (Platform.is_windows) "-windows" else if (Platform.is_macos) "-darwin" else "-linux")

    val info =
      platform_info.get(platform) getOrElse
        error("Bad platform identifier: " + quote(platform))

    if (Platform.is_windows && other_bash == "")
      error("Windows requires other bash (for msys)")


    /* bash */

    def bash(cwd: Path, script: String, echo: Boolean = false): Process_Result =
      progress.bash(
        if (other_bash == "") script else Bash.string(other_bash) + " -c " + Bash.string(script),
        cwd = cwd.file, echo = echo)


    /* configure and make */

    val configure_options =
      (if (!arch_64 && Isabelle_System.getenv("ISABELLE_PLATFORM64") == "x86_64-linux")
        info.options_multilib
       else info.options) ::: List("--enable-intinf-as-int") ::: options

    bash(root,
      info.setup + "\n" +
      """
        [ -f Makefile ] && make distclean
        {
          ./configure --prefix="$PWD/target" """ + Bash.strings(configure_options) + """
          rm -rf target
          make compiler && make compiler && make install
        } || { echo "Build failed" >&2; exit 2; }
      """, echo = true).check

    val ldd_files =
      if (Platform.is_linux) {
        val libs = bash(root, "ldd target/bin/poly").check.out_lines
        val Pattern = """\s*libgmp.*=>\s*(\S+).*""".r
        for (Pattern(lib) <- libs) yield lib
      }
      else Nil


    /* sha1 library */

    val sha1_files =
      if (sha1_root.isDefined) {
        val dir1 = sha1_root.get
        bash(dir1, "./build " + platform, echo = true).check
        val dir2 = dir1 + Path.explode(platform)
        File.read_dir(dir2).map(entry => dir2.implode + "/" + entry)
      }
      else Nil


    /* target */

    val target = Path.explode(platform)
    Isabelle_System.rm_tree(target)
    Isabelle_System.mkdirs(target)

    for {
      d <- List("target/bin", "target/lib")
      dir = root + Path.explode(d)
      entry <- File.read_dir(dir)
    } File.move(dir + Path.explode(entry), target)

    for (file <- "~~/Admin/polyml/polyi" :: info.copy_files ::: ldd_files ::: sha1_files)
      File.copy(Path.explode(file), target)
  }



  /** Isabelle tool wrapper **/

  val isabelle_tool = Isabelle_Tool("build_polyml", "build Poly/ML from sources", args =>
    {
      Command_Line.tool0 {
        var other_bash = ""
        var arch_64 = false
        var sha1_root: Option[Path] = None

        val getopts = Getopts("""
Usage: isabelle build_polyml [OPTIONS] ROOT [CONFIGURE_OPTIONS]

  Options are:
    -b EXE       other bash executable (notably for msys on Windows)
    -m ARCH      processor architecture (32=x86, 64=x86_64, default: x86)
    -s DIR       sha1 sources, see https://bitbucket.org/isabelle_project/sha1

  Build Poly/ML in the ROOT directory of its sources, with additional
  CONFIGURE_OPTIONS (e.g. --with-gmp).
""",
          "b:" -> (arg => other_bash = arg),
          "m:" ->
            {
              case "32" | "x86" => arch_64 = false
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
          arch_64 = arch_64, options = options, other_bash = other_bash)
      }
    })
}
