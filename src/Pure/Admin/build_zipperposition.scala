/*  Title:      Pure/Admin/build_zipperposition.scala
    Author:     Makarius

Build Isabelle Zipperposition component from OPAM repository.
*/

package isabelle


object Build_Zipperposition
{
  val default_version = "1.6"


  /* build Zipperposition */

  def build_zipperposition(
    version: String = default_version,
    verbose: Boolean = false,
    progress: Progress = new Progress,
    target_dir: Path = Path.current)
  {
    Isabelle_System.with_tmp_dir("build")(build_dir =>
    {
      Isabelle_System.require_command("patchelf")


      /* component */

      val component_name = "zipperposition-" + version
      val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component_name))
      progress.echo("Component " + component_dir)


      /* platform */

      val platform_name =
        proper_string(Isabelle_System.getenv("ISABELLE_PLATFORM64")) getOrElse
        error("No 64bit platform")

      val platform_dir = Isabelle_System.make_directory(component_dir + Path.basic(platform_name))


      /* build */

      progress.echo("OCaml/OPAM setup ...")
      progress.bash("isabelle ocaml_setup", echo = verbose).check

      progress.echo("Building Zipperposition for " + platform_name + " ...")
      progress.bash(cwd = build_dir.file, echo = verbose,
        script = "isabelle_opam install -y --destdir=" + File.bash_path(build_dir) +
          " zipperposition=" + Bash.string(version)).check


      /* install */

      File.copy(build_dir + Path.explode("doc/zipperposition/LICENSE"), component_dir)

      val prg_path = Path.basic("zipperposition")
      val exe_path = prg_path.platform_exe
      File.copy(build_dir + Path.basic("bin") + prg_path, platform_dir + exe_path)

      Executable.libraries_closure(
        platform_dir + exe_path, filter = Set("libgmp"), patchelf = true)


      /* settings */

      val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
      File.write(etc_dir + Path.basic("settings"),
        """# -*- shell-script -*- :mode=shellscript:

ISABELLE_ZIPPERPOSITION="$COMPONENT/$ISABELLE_PLATFORM64/zipperposition"
""")


      /* README */

      File.write(component_dir + Path.basic("README"),
"""This is Zipperposition """ + version + """ from the OCaml/OPAM repository.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    })
}


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_zipperposition", "build prover component from OPAM repository",
    args =>
    {
      var target_dir = Path.current
      var version = default_version
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_zipperposition [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -V VERSION   version (default: """" + default_version + """")
    -v           verbose

  Build prover component from OPAM repository.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "V:" -> (arg => version = arg),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      build_zipperposition(version = version, verbose = verbose, progress = progress,
        target_dir = target_dir)
    })
}
