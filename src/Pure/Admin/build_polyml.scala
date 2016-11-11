/*  Title:      Pure/Admin/build_polyml.scala
    Author:     Makarius

Build Poly/ML from sources.
*/

package isabelle


object Build_PolyML
{
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
        setup = "PATH=/usr/bin:/bin:/mingw32/bin",
        copy_files =
          List("/mingw32/bin/libgcc_s_dw2-1.dll",
            "/mingw32/bin/libgmp-10.dll",
            "/mingw32/bin/libstdc++-6.dll")),
    "x86_64-windows" ->
      Platform_Info(
        options =
          List("--host=x86_64-w64-mingw32", "CPPFLAGS=-I/mingw64/include", "--disable-windows-gui"),
        setup = "PATH=/usr/bin:/bin:/mingw64/bin",
        copy_files =
          List("/mingw64/bin/libgcc_s_seh-1.dll",
            "/mingw64/bin/libgmp-10.dll",
            "/mingw64/bin/libstdc++-6.dll")))

  lazy val default_platform = Isabelle_System.getenv_strict("ISABELLE_PLATFORM32")

  def build_polyml(
    source: Path,
    progress: Progress = Ignore_Progress,
    platform: String = default_platform,
    options: List[String] = Nil,
    other_bash: String = "")
  {
    source.is_dir || error("Bad source directory: " + source)

    val info =
      platform_info.get(platform) getOrElse
        error("Bad platform identifier: " + quote(platform))

    val multilib =
      platform == "x86-linux" && Isabelle_System.getenv("ISABELLE_PLATFORM64") == "x86_64-linux"

    val configure_options =
      (if (multilib) info.options_multilib else info.options) :::
        List("--enable-intinf-as-int") ::: options

    val script =
      info.setup + "\n" +
      """
        [ -f Makefile ] && make distclean
        {
          ./configure --prefix="$PWD/target" """ + Bash.strings(configure_options) + """
          rm -rf target
          make compiler && make compiler && make install
        } || { echo "Build failed" >&2; exit 2; }
      """

    Isabelle_System.bash(
      if (other_bash == "") script else Bash.string(other_bash) + " -c " + Bash.string(script),
      cwd = source.file, env = null,
      progress_stdout = progress.echo(_),
      progress_stderr = progress.echo(_)).check


    val target = Path.explode(platform)

    if (target.file.exists) {
      if (target.backup.file.exists) Isabelle_System.rm_tree(target.backup)
      File.move(target, target.backup)
    }
    Isabelle_System.mkdirs(target)

    for {
      d <- List("target/bin", "target/lib")
      dir = source + Path.explode(d)
      entry <- File.read_dir(dir)
    } File.move(dir + Path.explode(entry), target)

    for (file <- "~~/Admin/polyml/polyi" :: info.copy_files)
      File.copy(Path.explode(file), target)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_polyml", "build Poly/ML from sources", args =>
    {
      Command_Line.tool0 {
        var options = List.empty[String]
        var other_bash = ""
        var platform = default_platform

        val getopts = Getopts("""
Usage: isabelle build_polyml [OPTIONS] [SOURCE]

  Options are:
    -O OPTS...   additional options ./configure (e.g. --with-gmp)
    -b EXE       other bash executable (notably for msys on Windows)
    -p PLATFORM  platform identifier and target directory

  Build Poly/ML in SOURCE directory (default: .) for
  given PLATFORM (default: """ + default_platform + """).
""",
          "O:" -> (arg => options = options ::: List(arg)),
          "b:" -> (arg => other_bash = arg),
          "p:" -> (arg => platform = arg))

        val more_args = getopts(args)
        val source =
          more_args match {
            case Nil => Path.current
            case List(source) => Path.explode(source)
            case _ => getopts.usage()
          }
        build_polyml(source,
          progress = new Console_Progress, platform = platform, options = options,
            other_bash = other_bash)
      }
    }, admin = true)
}
