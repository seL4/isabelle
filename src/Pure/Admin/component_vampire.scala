/*  Title:      Pure/Admin/component_vampire.scala
    Author:     Makarius

Build Isabelle Vampire component from official download.
*/

package isabelle


object Component_Vampire {
  val default_download_url = "https://github.com/vprover/vampire/archive/refs/tags/v4.8HO4Sledgahammer.tar.gz"
  val default_version = "4.8"
  val default_jobs = 1

  def make_component_name(version: String): String =
    "vampire-" + Library.try_unprefix("v", version).getOrElse(version)


  /* build Vampire */

  def build_vampire(
    download_url: String = default_download_url,
    jobs: Int = default_jobs,
    component_name: String = "",
    component_version: String = default_version,
    progress: Progress = new Progress,
    target_dir: Path = Path.current
  ): Unit = {
    Isabelle_System.require_command("cmake")

    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      /* component */

      val Archive_Name = """^.*?([^/]+)$""".r

      val archive_name =
        download_url match {
          case Archive_Name(name) => name
          case _ => error("Failed to determine source archive name from " + quote(download_url))
        }

      if (component_version.isEmpty) error("Missing component version")

      val component = proper_string(component_name) getOrElse make_component_name(component_version)
      val component_dir =
        Components.Directory(target_dir + Path.basic(component)).create(progress = progress)


      /* platform */

      val platform_name = Isabelle_Platform.local.ISABELLE_PLATFORM()
      val platform_dir =
        Isabelle_System.make_directory(component_dir.path + Path.basic(platform_name))


      /* download source */

      val archive_path = tmp_dir + Path.basic(archive_name)
      Isabelle_System.download_file(download_url, archive_path, progress = progress)

      Isabelle_System.extract(archive_path, tmp_dir)
      val source_dir = File.get_dir(tmp_dir, title = download_url)

      Isabelle_System.extract(archive_path, component_dir.src, strip = true)


      /* build */

      progress.echo("Building Vampire for " + platform_name + " ...")

      Isabelle_System.copy_file(source_dir + Path.explode("LICENCE"), component_dir.path)

      val cmake_opts =
        "-DCMAKE_BUILD_TYPE=Release -DCMAKE_BUILD_HOL=On -DCMAKE_DISABLE_FIND_PACKAGE_Z3=ON " +
        (if (Platform.is_linux) "-DBUILD_SHARED_LIBS=0 " else "")
      val cmake_out =
        progress.bash("cmake " + cmake_opts + """-G "Unix Makefiles" .""",
          cwd = source_dir, echo = progress.verbose).check.out

      val Pattern = """-- Setting binary name to '?([^\s']*)'?""".r
      val binary =
        split_lines(cmake_out).collectFirst({ case Pattern(name) => name })
          .getOrElse(error("Failed to determine binary name from cmake output:\n" + cmake_out))

      progress.bash("make -j" + jobs, cwd = source_dir, echo = progress.verbose).check

      Isabelle_System.copy_file(source_dir + Path.basic("bin") + Path.basic(binary).platform_exe,
        platform_dir + Path.basic("vampire").platform_exe)


      /* settings */

      component_dir.write_settings("""
VAMPIRE_HOME="$COMPONENT/$ISABELLE_PLATFORM64"
VAMPIRE_VERSION=""" + quote(component_version) + """

ISABELLE_VAMPIRE="$VAMPIRE_HOME/vampire"
""")


      /* README */

      File.write(component_dir.README,
        "This Isabelle component provides Vampire " + component_version + """ using the
original sources from """ + download_url + """

The executables have been built via "cmake . && make"


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_vampire", "build prover component from official download",
    Scala_Project.here,
    { args =>
      var target_dir = Path.current
      var download_url = default_download_url
      var jobs = default_jobs
      var component_name = ""
      var component_version = default_version
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle component_vampire [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL
                 (default: """" + default_download_url + """")
    -j NUMBER    parallel jobs for make (default: """ + default_jobs + """)
    -n NAME      component name (default: """" + make_component_name("VERSION") + """")
    -V VERSION   component version (default: """ + default_version + """)
    -v           verbose

  Build prover component from official download.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "U:" -> (arg => download_url = arg),
        "j:" -> (arg => jobs = Value.Nat.parse(arg)),
        "n:" -> (arg => component_name = arg),
        "V:" -> (arg => component_version = arg),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress(verbose = verbose)

      build_vampire(download_url = download_url, component_name = component_name,
        component_version = component_version, jobs = jobs, progress = progress,
        target_dir = target_dir)
    })
}
