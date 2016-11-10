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
    shell_path: String = "",
    copy_files: List[String] = Nil)

  private val platform_info = Map(
    "x86-linux" ->
      Platform_Info(
        options_multilib =
          List("--build=i386", "CFLAGS='-m32 -O3'", "CXXFLAGS='-m32 -O3'", "CCASFLAGS='-m32'")),
    "x86_64-linux" -> Platform_Info(),
    "x86-darwin" ->
      Platform_Info(
        options =
          List("--build=i686-darwin", "CFLAGS='-arch i686 -O3 -I../libffi/include'",
            "CXXFLAGS='-arch i686 -O3", "-I../libffi/include'", "CCASFLAGS='-arch i686 -O3'",
            "LDFLAGS='-segprot POLY rwx rwx'")),
    "x86_64-darwin" ->
      Platform_Info(
        options =
          List("--build=x86_64-darwin", "CFLAGS='-arch x86_64 -O3 -I../libffi/include'",
            "CXXFLAGS='-arch x86_64 -O3 -I../libffi/include'", "CCASFLAGS='-arch x86_64'",
            "LDFLAGS='-segprot POLY rwx rwx'")),
    "x86-windows" ->
      Platform_Info(
        options =
          List("--host=i686-w32-mingw32", "CPPFLAGS='-I/mingw32/include'", "--disable-windows-gui"),
        shell_path = "/mingw32/bin",
        copy_files =
          List("/mingw32/bin/libgcc_s_dw2-1.dll",
            "/mingw32/bin/libgmp-10.dll",
            "/mingw32/bin/libstdc++-6.dll")),
    "x86_64-windows" ->
      Platform_Info(
        options =
          List("--host=x86_64-w64-mingw32", "CPPFLAGS='-I/mingw64/include'", "--disable-windows-gui"),
        shell_path = "/mingw64/bin",
        copy_files =
          List("/mingw64/bin/libgcc_s_seh-1.dll",
            "/mingw64/bin/libgmp-10.dll",
            "/mingw64/bin/libstdc++-6.dll")))

  lazy val default_platform = Isabelle_System.getenv_strict("ISABELLE_PLATFORM32")

  def build_polyml(
    source: Path,
    progress: Progress = Ignore_Progress,
    platform: String = default_platform,
    multilib: Boolean = false,
    options: List[String] = Nil)
  {
    source.is_dir || error("Bad source directory: " + source)

    val info =
      platform_info.get(platform) getOrElse
        error("Bad platform identifier: " + quote(platform))

    val target = Path.explode(platform)

    val configure_options =
      info.options ::: List("--enable-intinf-as-int") ::: options :::
      (if (multilib) info.options_multilib else info.options)

    Isabelle_System.bash(cwd = source.file,
      script =
        (if (info.shell_path == "") "" else "export PATH=\"" + info.shell_path + ":$PATH\"\n") +
        """
          make distclean
          {
            ./configure """ + quote("--prefix=$PWD/" + platform) + " " + Bash.strings(options) + """
            make compiler && make compiler && make install
          } || { echo "Build failed" >&2; exit 2; }
        """,
        progress_stdout = progress.echo(_),
        progress_stderr = progress.echo(_)).check

    if (target.file.exists) {
      if (target.backup.file.exists) Isabelle_System.rm_tree(target.backup)
      File.move(target, target.backup)
    }
    Isabelle_System.mkdirs(target)

    for {
      d <- List("bin", "lib")
      dir = source + Path.explode(platform) + Path.explode(d)
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
        var multilib = false
        var options = List.empty[String]
        var platform = default_platform

        val getopts = Getopts("""
Usage: isabelle build_polyml [OPTIONS] SOURCE

  Options are:
    -M           compile for 32bit multilib (for x86-linux on x86_64-linux)
    -O OPTS...   additional options ./configure (e.g. --with-gmp)
    -p PLATFORM  platform identifier and target directory

  Build Poly/ML in SOURCE directory for given PLATFORM (default: """ + default_platform + """).
""",
          "M" -> (_ => multilib = true),
          "O:" -> (arg => options = options ::: List(arg)),
          "p:" -> (arg => platform = arg))

        val more_args = getopts(args)
        more_args match {
          case List(source) =>
            build_polyml(Path.explode(source), progress = new Console_Progress,
              platform = platform, multilib = multilib, options = options)
          case _ => getopts.usage()
        }
      }
    }, admin = true)
}
