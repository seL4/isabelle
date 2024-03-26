/*  Title:      Pure/Admin/component_minisat.scala
    Author:     Makarius

Build Isabelle Minisat from sources.
*/

package isabelle


object Component_Minisat {
  val default_download_url = "https://github.com/stp/minisat/archive/releases/2.2.1.tar.gz"

  def make_component_name(version: String): String = "minisat-" + version


  /* build Minisat */

  def build_minisat(
    download_url: String = default_download_url,
    component_name: String = "",
    progress: Progress = new Progress,
    target_dir: Path = Path.current
  ): Unit = {
    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      /* component */

      val Archive_Name = """^.*?([^/]+)$""".r
      val Version = """^v?([0-9.]+)\.tar.gz$""".r

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

      val component = proper_string(component_name) getOrElse make_component_name(version)
      val component_dir =
        Components.Directory(target_dir + Path.basic(component)).create(progress = progress)


      /* platform */

      val platform_name =
        proper_string(Isabelle_System.getenv("ISABELLE_PLATFORM64")) getOrElse
          error("Missing ISABELLE_PLATFORM64")

      val platform_dir =
        Isabelle_System.make_directory(component_dir.path + Path.basic(platform_name))


      /* download source */

      val archive_path = tmp_dir + Path.basic(archive_name)
      Isabelle_System.download_file(download_url, archive_path, progress = progress)

      Isabelle_System.extract(archive_path, tmp_dir)
      val source_dir = File.get_dir(tmp_dir, title = download_url)

      Isabelle_System.extract(archive_path, component_dir.src, strip = true)


      /* build */

      progress.echo("Building Minisat for " + platform_name + " ...")

      Isabelle_System.copy_file(source_dir + Path.explode("LICENSE"), component_dir.path)

      if (Platform.is_macos) {
        File.change(source_dir + Path.explode("Makefile")) {
          _.replaceAll("--static", "").replaceAll("-Wl,-soname\\S+", "")
        }
      }
      progress.bash("make r", source_dir.file, echo = progress.verbose).check

      Isabelle_System.copy_file(
        source_dir + Path.explode("build/release/bin/minisat").platform_exe, platform_dir)

      if (Platform.is_windows) {
        Isabelle_System.copy_file(Path.explode("/bin/cygwin1.dll"), platform_dir)
      }


      /* settings */

      component_dir.write_settings("""
MINISAT_HOME="$COMPONENT/$ISABELLE_PLATFORM64"

ISABELLE_MINISAT="$MINISAT_HOME/minisat"
""")


      /* README */

      File.write(component_dir.README,
        "This Isabelle component provides Minisat " + version + """ using the
sources from """ + download_url + """

The executables have been built via "make r"; macOS requires to
remove options "--static" and "-Wl,-soname,..." from the Makefile.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_minisat", "build prover component from sources", Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_download_url
        var component_name = ""
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_minisat [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL
                 (default: """" + default_download_url + """")
    -n NAME      component name (default: """" + make_component_name("VERSION") + """")
    -v           verbose

  Build prover component from official download.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg),
          "n:" -> (arg => component_name = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        build_minisat(download_url = download_url, component_name = component_name,
          progress = progress, target_dir = target_dir)
      })
}
