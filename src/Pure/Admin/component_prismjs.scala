/*  Title:      Pure/Admin/component_prismjs.scala
    Author:     Makarius

Build Isabelle component for the Prism.js syntax highlighter.

See also:
  - https://prismjs.com
  - https://www.npmjs.com/package/prismjs
*/

package isabelle


object Component_Prismjs {
  /* build prismjs component */

  val default_version = "1.29.0"

  def build_prismjs(
    version: String = default_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    /* component name */

    val component = "prismjs-" + version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component)).create(progress = progress)


    /* download */

    Isabelle_System.with_tmp_dir("tmp") { tmp_dir =>
      val node_dir =
        Nodejs.setup(tmp_dir, platform_context = Isabelle_Platform.Context(progress = progress))
      Isabelle_System.bash(
        Library.make_lines(
          "set -e",
          node_dir.path_setup,
          "npm init -y",
          "npm install prismjs@" + Bash.string(version)),
        cwd = tmp_dir).check
      Isabelle_System.copy_dir(tmp_dir + Path.explode("node_modules/prismjs"),
        component_dir.path, direct = true)
    }


    /* settings */

    component_dir.write_settings("""
ISABELLE_PRISMJS_HOME="$COMPONENT"
""")


    /* README */

    File.write(component_dir.README,
      """This is Prism.js """ + version + """ from https://www.npmjs.com/package/prismjs


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_prismjs", "build component for prismjs",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle component_prismjs [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -V VERSION   version (default: """" + default_version + """")

  Build component for Prism.js.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "V:" -> (arg => version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_prismjs(version = version, target_dir = target_dir, progress = progress)
      })
}
