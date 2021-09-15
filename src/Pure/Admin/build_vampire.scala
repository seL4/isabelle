/*  Title:      Pure/Admin/build_vampire.scala
    Author:     Makarius

Build Isabelle Vampire component from repository.
*/

package isabelle


object Build_Vampire
{
  val default_repository = "https://github.com/vprover/vampire.git"
  val default_version1 = "4.5.1"
  val default_version2 = "df87588848db"
  val default_jobs = 1

  def make_component_name(version: String): String = "vampire-" + version


  /* build Vampire */

  def build_vampire(
    repository: String = default_repository,
    version1: String = default_version1,
    version2: String = default_version2,
    jobs: Int = default_jobs,
    component_name: String = "",
    verbose: Boolean = false,
    progress: Progress = new Progress,
    target_dir: Path = Path.current): Unit =
  {
    Isabelle_System.require_command("git")
    Isabelle_System.require_command("cmake")

    Isabelle_System.with_tmp_dir("build")(tmp_dir =>
    {
      /* component and platform */

      val component = proper_string(component_name) getOrElse make_component_name(version1)
      val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component))
      progress.echo("Component " + component_dir)

      val platform_name =
        proper_string(Isabelle_System.getenv("ISABELLE_PLATFORM64")) getOrElse
          error("No 64bit platform")
      val platform_dir = Isabelle_System.make_directory(component_dir + Path.basic(platform_name))


      /* clone repository */

      progress.echo("Cloning repository " + repository)
      progress.bash("git clone " + Bash.string(repository) + " vampire",
        cwd = tmp_dir.file, echo = verbose).check

      val source_dir = tmp_dir + Path.explode("vampire")

      Isabelle_System.copy_file(source_dir + Path.explode("LICENCE"), component_dir)


      /* build versions */

      for { (rev, exe) <- List(version1 -> "vampire", version2 -> "vampire_polymorphic") } {
        progress.echo("Building " + exe + " (rev " + rev + ")")
        progress.bash("git checkout --quiet --detach " + Bash.string(rev),
          cwd = source_dir.file, echo = verbose).check

        val build_dir = source_dir + Path.explode("build")
        Isabelle_System.rm_tree(build_dir)
        Isabelle_System.make_directory(build_dir)

        val cmake_opts = if (Platform.is_linux) "-DBUILD_SHARED_LIBS=0 " else ""
        val cmake_out =
          progress.bash("cmake " + cmake_opts + """-G "Unix Makefiles" ..""",
            cwd = build_dir.file, echo = verbose).check.out

        val Pattern = """-- Setting binary name to '?([^\s']*)'?""".r
        val binary =
          split_lines(cmake_out).collectFirst({ case Pattern(name) => name })
            .getOrElse(error("Failed to determine binary name from cmake output:\n" + cmake_out))

        progress.bash("make -j" + jobs, cwd = build_dir.file, echo = verbose).check

        Isabelle_System.copy_file(build_dir + Path.basic("bin") + Path.basic(binary).platform_exe,
          platform_dir + Path.basic(exe).platform_exe)
      }


      /* settings */

      val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
      File.write(etc_dir + Path.basic("settings"),
        """# -*- shell-script -*- :mode=shellscript:

VAMPIRE_HOME="$COMPONENT/$ISABELLE_PLATFORM64"

ISABELLE_VAMPIRE="$VAMPIRE_HOME/vampire"
ISABELLE_VAMPIRE_POLYMORPHIC="$VAMPIRE_HOME/vampire_polymorphic"

VAMPIRE_EXTRA_OPTIONS=""
""")


      /* README */

      File.write(component_dir + Path.basic("README"),
        "This Isabelle component provides two versions of Vampire from\n" + repository + """

  * vampire: standard version (regular stable release)
  * vampire_polymorphic: special version for polymorphic FOL and HOL
    (intermediate repository version)

The executables have been built like this:

    git checkout COMMIT
    cmake .
    make

The precise commit id is revealed by executing "vampire --version".


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_vampire", "build prover component from repository", Scala_Project.here,
    args =>
    {
      var target_dir = Path.current
      var repository = default_repository
      var version1 = default_version1
      var version2 = default_version2
      var jobs = default_jobs
      var component_name = ""
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_vampire [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       repository (default: """" + default_repository + """")
    -V REV1      standard version (default: """" + default_version1 + """")
    -W REV2      polymorphic version (default: """" + default_version2 + """")
    -j NUMBER    parallel jobs for make (default: """ + default_jobs + """)
    -n NAME      component name (default: """" + make_component_name("REV1") + """")
    -v           verbose

  Build prover component from official download.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "U:" -> (arg => repository = arg),
        "V:" -> (arg => version1 = arg),
        "W:" -> (arg => version2 = arg),
        "j:" -> (arg => jobs = Value.Nat.parse(arg)),
        "n:" -> (arg => component_name = arg),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      build_vampire(repository = repository, version1 = version1, version2 = version2,
        component_name = component_name, jobs = jobs, verbose = verbose, progress = progress,
        target_dir = target_dir)
    })
}
