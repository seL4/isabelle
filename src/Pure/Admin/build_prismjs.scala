/*  Title:      Pure/Admin/build_prismjs.scala
    Author:     Makarius

Build Isabelle component for the Prism.js syntax highlighter.

See also:
  - https://prismjs.com
  - https://www.npmjs.com/package/prismjs
*/

package isabelle


object Build_Prismjs {
  /* build prismjs component */

  val default_version = "1.29.0"

  def build_prismjs(
    version: String = default_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    Isabelle_System.require_command("npm", test = "help")


    /* component name */

    val component = "prismjs-" + version
    val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component))
    progress.echo("Component " + component_dir)


    /* download */

    Isabelle_System.with_tmp_dir("tmp") { tmp_dir =>
      Isabelle_System.bash("npm init -y && npm install prismjs@" + Bash.string(version),
        cwd = tmp_dir.file).check

      component_dir.file.delete()
      Isabelle_System.copy_dir(tmp_dir + Path.explode("node_modules/prismjs"),
        component_dir)
    }


    /* settings */

    val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
    File.write(etc_dir + Path.basic("settings"),
      """# -*- shell-script -*- :mode=shellscript:

ISABELLE_PRISMJS_HOME="$COMPONENT"
""")


    /* README */

    File.write(component_dir + Path.basic("README"),
      """This is Prism.js """ + version + """ from https://www.npmjs.com/package/prismjs


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_prismjs", "build component for prismjs",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle build_prismjs [OPTIONS]

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
