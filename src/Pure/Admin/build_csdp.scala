/*  Title:      Pure/Admin/build_csdp.scala
    Author:     Makarius

Build Isabelle CSDP component from official download.
*/

package isabelle


object Build_CSDP
{
  // Note: version 6.2.0 does not quite work for the "sos" proof method
  val default_download_url = "https://github.com/coin-or/Csdp/archive/releases/6.1.1.tar.gz"


  /* flags */

  sealed case class Flags(platform: String, CFLAGS: String = "", LIBS: String = "")
  {
    val changed: List[(String, String)] =
      List("CFLAGS" -> CFLAGS, "LIBS" -> LIBS).filter(p => p._2.nonEmpty)

    def print: Option[String] =
      if (changed.isEmpty) None
      else
        Some("  * " + platform + ":\n" + changed.map(p => "    " + p._1 + "=" + p._2)
          .mkString("\n"))

    def change(path: Path)
    {
      def change_line(line: String, entry: (String, String)): String =
        line.replaceAll(entry._1 + "=.*", entry._1 + "=" + entry._2)
      File.change(path, s =>
        split_lines(s).map(line => (line /: changed)(change_line)).mkString("\n"))
    }
  }

  val build_flags: List[Flags] =
    List(
      Flags("arm64-linux",
        CFLAGS = "-O3 -ansi -Wall -DNOSHORTS -DBIT64 -DUSESIGTERM -DUSEGETTIME -I../include",
        LIBS = "-static -L../lib -lsdp -llapack -lblas -lgfortran -lm"),
      Flags("x86_64-linux",
        CFLAGS = "-O3 -ansi -Wall -DNOSHORTS -DBIT64 -DUSESIGTERM -DUSEGETTIME -I../include",
        LIBS = "-static -L../lib -lsdp -llapack -lblas -lgfortran -lquadmath -lm"),
      Flags("x86_64-darwin",
        CFLAGS = "-O3 -Wall -DNOSHORTS -DBIT64 -DUSESIGTERM -DUSEGETTIME -I../include",
        LIBS = "-L../lib -lsdp -llapack -lblas -lm"),
      Flags("x86_64-windows"))


  /* build CSDP */

  def build_csdp(
    download_url: String = default_download_url,
    verbose: Boolean = false,
    progress: Progress = new Progress,
    target_dir: Path = Path.current,
    mingw: MinGW = MinGW.none)
  {
    mingw.check

    Isabelle_System.with_tmp_dir("build")(tmp_dir =>
    {
      /* component */

      val Archive_Name = """^.*?([^/]+)$""".r
      val Version = """^[^0-9]*([0-9].*)\.tar.gz$""".r

      val archive_name =
        download_url match {
          case Archive_Name(name) => name
          case _ => error("Failed to determine source archive name from " + quote(download_url))
        }

      val version =
        archive_name match {
          case Version(version) => version
          case _ => error("Failed to determine component version from " + quote(archive_name))
        }

      val component_name = "csdp-" + version
      val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component_name))
      progress.echo("Component " + component_dir)


      /* platform */

      val platform_name =
        proper_string(Isabelle_System.getenv("ISABELLE_WINDOWS_PLATFORM64")) orElse
        proper_string(Isabelle_System.getenv("ISABELLE_PLATFORM64")) getOrElse
        error("No 64bit platform")

      val platform_dir = Isabelle_System.make_directory(component_dir + Path.basic(platform_name))


      /* download source */

      val archive_path = tmp_dir + Path.basic(archive_name)
      Isabelle_System.download(download_url, archive_path, progress = progress)

      Isabelle_System.bash("tar xzf " + File.bash_path(archive_path), cwd = tmp_dir.file).check
      val source_name = File.get_dir(tmp_dir)

      Isabelle_System.bash(
        "tar xzf " + archive_path + " && mv " + Bash.string(source_name) + " src",
        cwd = component_dir.file).check


      /* build */

      progress.echo("Building CSDP for " + platform_name + " ...")

      val build_dir = tmp_dir + Path.basic(source_name)
      build_flags.find(flags => flags.platform == platform_name) match {
        case None => error("No build flags for platform " + quote(platform_name))
        case Some(flags) =>
          File.find_files(build_dir.file, pred = file => file.getName == "Makefile").
            foreach(file => flags.change(File.path(file)))
      }

      progress.bash(mingw.bash_script("make"), cwd = build_dir.file, echo = verbose).check


      /* install */

      Isabelle_System.copy_file(build_dir + Path.explode("LICENSE"), component_dir)
      Isabelle_System.copy_file(build_dir + Path.explode("solver/csdp").platform_exe, platform_dir)

      if (Platform.is_windows) {
        Executable.libraries_closure(platform_dir + Path.explode("csdp.exe"), mingw = mingw,
          filter =
            Set("libblas", "liblapack", "libgfortran", "libgcc_s_seh",
              "libquadmath", "libwinpthread"))
      }


      /* settings */

      val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
      File.write(etc_dir + Path.basic("settings"),
        """# -*- shell-script -*- :mode=shellscript:

ISABELLE_CSDP="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-$ISABELLE_PLATFORM64}/csdp"
""")


      /* README */

      File.write(component_dir + Path.basic("README"),
"""This is CSDP """ + version + """ from
""" + download_url + """

Makefile flags have been changed for various platforms as follows:

""" + build_flags.flatMap(_.print).mkString("\n\n") + """

The distribution has been built like this:

    cd src && make

Only the bare "solver/csdp" program is used for Isabelle.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    })
}


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_csdp", "build prover component from official download", Scala_Project.here,
    args =>
    {
      var target_dir = Path.current
      var mingw = MinGW.none
      var download_url = default_download_url
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_csdp [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -M DIR       msys/mingw root specification for Windows
    -U URL       download URL
                 (default: """" + default_download_url + """")
    -v           verbose

  Build prover component from official download.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "M:" -> (arg => mingw = MinGW(Path.explode(arg))),
        "U:" -> (arg => download_url = arg),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      build_csdp(download_url = download_url, verbose = verbose, progress = progress,
        target_dir = target_dir, mingw = mingw)
    })
}
