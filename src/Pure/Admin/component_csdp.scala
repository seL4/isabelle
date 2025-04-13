/*  Title:      Pure/Admin/component_csdp.scala
    Author:     Makarius

Build Isabelle CSDP component from official download.
*/

package isabelle


object Component_CSDP {
  // Note: version 6.2.0 does not quite work for the "sos" proof method
  val default_download_url = "https://github.com/coin-or/Csdp/archive/releases/6.1.1.tar.gz"


  /* flags */

  sealed case class Flags(platform: String, CFLAGS: String = "", LIBS: String = "") {
    val changed: List[(String, String)] =
      List("CFLAGS" -> CFLAGS, "LIBS" -> LIBS).filter(p => p._2.nonEmpty)

    def print: Option[String] =
      if (changed.isEmpty) None
      else
        Some("  * " + platform + ":\n" + changed.map(p => "    " + Properties.Eq(p))
          .mkString("\n"))

    def change(path: Path): Unit = {
      def change_line(line: String, p: (String, String)): String =
        line.replaceAll(p._1 + "=.*", Properties.Eq(p))
      File.change_lines(path) { _.map(line => changed.foldLeft(line)(change_line)) }
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
    progress: Progress = new Progress,
    target_dir: Path = Path.current,
    mingw: MinGW = MinGW.none
  ): Unit = {
    mingw.check()

    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
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
      val component_dir =
        Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)


      /* platform */

      val platform_name = Isabelle_Platform.self.ISABELLE_PLATFORM(windows = true)
      val platform_dir =
        Isabelle_System.make_directory(component_dir.path + Path.basic(platform_name))


      /* download source */

      val archive_path = tmp_dir + Path.basic(archive_name)
      Isabelle_System.download_file(download_url, archive_path, progress = progress)

      Isabelle_System.extract(archive_path, tmp_dir)
      val source_dir = File.get_dir(tmp_dir, title = download_url)

      Isabelle_System.extract(archive_path, component_dir.src, strip = true)


      /* build */

      progress.echo("Building CSDP for " + platform_name + " ...")

      build_flags.find(flags => flags.platform == platform_name) match {
        case None => error("No build flags for platform " + quote(platform_name))
        case Some(flags) =>
          File.find_files(source_dir.file, pred = file => file.getName == "Makefile").
            foreach(file => flags.change(File.path(file)))
      }

      progress.bash(mingw.bash_script("make"),
        cwd = source_dir,
        echo = progress.verbose).check


      /* install */

      Isabelle_System.copy_file(source_dir + Path.explode("LICENSE"), component_dir.path)
      Isabelle_System.copy_file(source_dir + Path.explode("solver/csdp").platform_exe, platform_dir)

      if (Platform.is_windows) {
        Executable.library_closure(platform_dir + Path.explode("csdp.exe"), mingw = mingw,
          filter =
            Set("libblas", "liblapack", "libgfortran", "libgcc_s_seh",
              "libquadmath", "libwinpthread"))
      }


      /* settings */

      component_dir.write_settings("""
ISABELLE_CSDP="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-$ISABELLE_PLATFORM64}/csdp"
""")


      /* README */

      File.write(component_dir.README,
"""This is CSDP """ + version + """ from
""" + download_url + """

Makefile flags have been changed for various platforms as follows:

""" + build_flags.flatMap(_.print).mkString("\n\n") + """

The distribution has been built like this:

    cd src && make

Only the bare "solver/csdp" program is used for Isabelle.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    }
}


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_csdp", "build prover component from official download", Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var mingw = MinGW.none
        var download_url = default_download_url
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_csdp [OPTIONS]

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

        val progress = new Console_Progress(verbose = verbose)

        build_csdp(download_url = download_url, progress = progress,
          target_dir = target_dir, mingw = mingw)
      })
}
