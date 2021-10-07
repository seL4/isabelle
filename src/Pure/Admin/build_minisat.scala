/*  Title:      Pure/Admin/build_minisat.scala
    Author:     Makarius

Build Isabelle Minisat from sources.
*/

package isabelle


object Build_Minisat
{
  val default_download_url = "https://github.com/stp/minisat/archive/releases/2.2.1.tar.gz"

  def make_component_name(version: String): String = "minisat-" + version


  /* build Minisat */

  def build_minisat(
    download_url: String = default_download_url,
    component_name: String = "",
    verbose: Boolean = false,
    progress: Progress = new Progress,
    target_dir: Path = Path.current): Unit =
  {
    Isabelle_System.with_tmp_dir("build")(tmp_dir =>
    {
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
      val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component))
      progress.echo("Component " + component_dir)


      /* platform */

      val platform_name =
        proper_string(Isabelle_System.getenv("ISABELLE_PLATFORM64")) getOrElse
          error("No 64bit platform")

      val platform_dir = Isabelle_System.make_directory(component_dir + Path.basic(platform_name))


      /* download source */

      val archive_path = tmp_dir + Path.basic(archive_name)
      Isabelle_System.download_file(download_url, archive_path, progress = progress)

      Isabelle_System.bash("tar xzf " + File.bash_path(archive_path), cwd = tmp_dir.file).check
      val source_name = File.get_dir(tmp_dir)

      Isabelle_System.bash(
        "tar xzf " + archive_path + " && mv " + Bash.string(source_name) + " src",
        cwd = component_dir.file).check


      /* build */

      progress.echo("Building Minisat for " + platform_name + " ...")

      val build_dir = tmp_dir + Path.basic(source_name)
      Isabelle_System.copy_file(build_dir + Path.explode("LICENSE"), component_dir)

      progress.bash("make r", build_dir.file, echo = verbose).check

      Isabelle_System.copy_file(
        build_dir + Path.explode("build/release/bin/minisat").platform_exe, platform_dir)


      /* settings */

      val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
      File.write(etc_dir + Path.basic("settings"),
        """# -*- shell-script -*- :mode=shellscript:

MINISAT_HOME="$COMPONENT/$ISABELLE_PLATFORM64"

ISABELLE_MINISAT="$MINISAT_HOME/minisat"
""")


      /* README */

      File.write(component_dir + Path.basic("README"),
        "This Isabelle component provides Minisat " + version + """using the
sources from """.stripMargin + download_url + """

The executables have been built via "make r".


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_minisat", "build prover component from sources", Scala_Project.here,
    args =>
    {
      var target_dir = Path.current
      var download_url = default_download_url
      var component_name = ""
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_minisat [OPTIONS]

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

      val progress = new Console_Progress()

      build_minisat(download_url = download_url, component_name = component_name,
        verbose = verbose, progress = progress, target_dir = target_dir)
    })
}
