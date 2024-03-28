/*  Title:      Pure/Admin/component_verit.scala
    Author:     Makarius

Build Isabelle veriT component from official download.
*/

package isabelle


object Component_VeriT {
  val default_download_url = "https://verit.loria.fr/rmx/2021.06.2/verit-2021.06.2-rmx.tar.gz"


  /* build veriT */

  def build_verit(
    download_url: String = default_download_url,
    progress: Progress = new Progress,
    target_dir: Path = Path.current,
    mingw: MinGW = MinGW.none
  ): Unit = {
    mingw.check

    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      /* component */

      val Archive_Name = """^.*?([^/]+)$""".r
      val Version = """^[^-]+-(.+)\.tar.gz$""".r

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

      val component_name = "verit-" + version
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

      progress.echo("Building veriT for " + platform_name + " ...")

      val configure_options =
        if (Platform.is_linux) "LDFLAGS=-Wl,-rpath,_DUMMY_" else ""

      progress.bash(mingw.bash_script("set -e\n./configure " + configure_options + "\nmake"),
        cwd = source_dir.file, echo = progress.verbose).check


      /* install */

      Isabelle_System.copy_file(source_dir + Path.explode("LICENSE"), component_dir.path)

      val exe_path = Path.basic("veriT").platform_exe
      Isabelle_System.copy_file(source_dir + exe_path, platform_dir)
      Executable.libraries_closure(platform_dir + exe_path, filter = Set("libgmp"), mingw = mingw)


      /* settings */

      component_dir.write_settings("""
ISABELLE_VERIT="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-$ISABELLE_PLATFORM64}/veriT"
""")


      /* README */

      File.write(component_dir.README,
"""This is veriT """ + version + """ from
""" + download_url + """

It has been built from sources like this:

  cd src
  ./configure
  make


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    }
}


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_verit", "build prover component from official download",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var mingw = MinGW.none
        var download_url = default_download_url
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_verit [OPTIONS]

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

        build_verit(download_url = download_url, progress = progress,
          target_dir = target_dir, mingw = mingw)
      })
}
