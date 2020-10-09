/*  Title:      Pure/Admin/build_csdp.scala
    Author:     Makarius

Build Isabelle CSDP component from official downloads.
*/

package isabelle


object Build_CSDP
{
  /* build CSDP */

  val component_name = "csdp-6.2.0"

  val source_url = "https://github.com/coin-or/Csdp/archive/releases/6.2.0.tar.gz"
  val windows_url = "https://github.com/coin-or/Csdp/files/2485584/csdp6.2.0win64.zip"

  sealed case class Flags(platform: String, CFLAGS: String = "", LIBS: String = "")
  {
    def print: String =
      "  * " + platform + ":\n" +
      List("CFLAGS=" + CFLAGS, "LIBS=" + LIBS).map("    " + _).mkString("\n")

    def change(path: Path)
    {
      File.change(path, s =>
        (for (line <- split_lines(s))
          yield {
            line.replaceAll("CFLAGS=.*", "CFLAGS=" + CFLAGS)
              .replaceAll("LIBS=.*", "LIBS=" + LIBS)
          }).mkString("\n"))
    }
  }

  val build_flags: List[Flags] =
    List(
      Flags("arm64-linux",
        CFLAGS = "-march=native -mtune=native -Ofast -ansi -Wall -DBIT64 -DUSESIGTERM -DUSEGETTIME -I../include",
        LIBS = "-static -L../lib -lsdp -llapack -lblas -lgfortran -lm"),
      Flags("x86_64-linux",  // Ubuntu 16.04 LTS
        CFLAGS = "-march=native -mtune=native -Ofast -ansi -Wall -DBIT64 -DUSESIGTERM -DUSEGETTIME -I../include",
        LIBS = "-static -L../lib -lsdp -llapack -lblas -lgfortran -lquadmath -lm"),
      Flags("x86_64-darwin",
        CFLAGS = "-m64 -Ofast -ansi -Wall -DBIT64 -DUSESIGTERM -DUSEGETTIME -I../include",
        LIBS = "-L../lib -lsdp -llapack -lblas -lm"))

  def build_csdp(
    pretend_windows: Boolean = false,
    verbose: Boolean = false,
    progress: Progress = new Progress,
    target_dir: Path = Path.current)
  {
    Isabelle_System.with_tmp_dir("build")(tmp_dir =>
    {
      val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component_name))
      progress.echo("Component " + component_dir)


      /* platform */

      val is_windows = Platform.is_windows || pretend_windows

      val (platform_name, windows_name) =
        if (is_windows) {
          val Windows_Name = """^.*?([^/]+)\.zip$""".r
          val windows_name =
            windows_url match {
              case Windows_Name(name) => name
              case _ => error("Failed to determine base name from " + quote(windows_url))
            }
          ("x86_64-windows", windows_name)
        }
        else {
          val name =
            proper_string(Isabelle_System.getenv("ISABELLE_PLATFORM64"))
              .getOrElse(error("No 64bit platform"))
          (name, "")
        }

      val platform_dir = Isabelle_System.make_directory(component_dir + Path.basic(platform_name))


      /* download */

      val archive_path = tmp_dir + Path.basic("src.tar.gz")
      Isabelle_System.download(source_url, archive_path, progress = progress)

      Isabelle_System.bash("tar xzf src.tar.gz", cwd = tmp_dir.file).check
      val source_name =
        File.read_dir(tmp_dir).filterNot(_ == "src.tar.gz") match {
          case List(name) => name
          case _ => error("Exactly one entry expected in archive " + quote(source_url))
        }
      Isabelle_System.bash(
        "tar xzf " + archive_path + " && mv " + Bash.string(source_name) + " src",
        cwd = component_dir.file).check


      /* build */

      if (is_windows) {
        Isabelle_System.download(windows_url, tmp_dir + Path.basic("windows.zip"),
          progress = progress)
        Isabelle_System.bash("unzip -x windows", cwd = tmp_dir.file).check

        val windows_dir = tmp_dir + Path.explode(windows_name)
        File.copy(windows_dir + Path.explode("LICENSE"), component_dir)
        File.copy(windows_dir + Path.explode("bin/csdp.exe"), platform_dir)
        File.set_executable(platform_dir + Path.basic("csdp.exe"), true)
      }
      else {
        progress.echo("Building CSDP ...")

        val build_dir = tmp_dir + Path.basic(source_name)
        build_flags.find(flags => flags.platform == platform_name) match {
          case None => error("No build flags for platform " + quote(platform_name))
          case Some(flags) => flags.change(build_dir + Path.basic("Makefile"))
        }
        Isabelle_System.bash("make",
          cwd = build_dir.file,
          progress_stdout = progress.echo_if(verbose, _),
          progress_stderr = progress.echo_if(verbose, _)).check
        File.copy(build_dir + Path.explode("solver/csdp"), platform_dir)
      }


      /* settings */

      val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
      File.write(etc_dir + Path.basic("settings"),
        """# -*- shell-script -*- :mode=shellscript:

ISABELLE_CSDP="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-$ISABELLE_PLATFORM64}/csdp"
""")


      /* README */

      File.write(component_dir + Path.basic("README"),
"""This distribution of CSDP is based on the official downloads:
""" + source_url + """
""" + windows_url + """

For Linux and macOS, it has been built from sources using the following
options in the Makefile:

""" + build_flags.map(_.print).mkString("\n\n") + """

For Windows, the existing binary distribution has been used.

Only the bare "csdp" program is required for Isabelle.


    Makarius
    """ + Date.Format.date(Date.now()) + "\n")
    })
}


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_csdp", "build prover component from official downloads",
    args =>
    {
      var target_dir = Path.current
      var pretend_windows = false
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_csdp [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -W           pretend that platform is Windows: download binary, no build
    -v           verbose

  Build prover component from official downloads.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "W" -> (_ => pretend_windows = true),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      build_csdp(pretend_windows = pretend_windows, verbose = verbose, progress = progress,
        target_dir = target_dir)
    })
}
