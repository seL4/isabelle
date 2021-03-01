/*  Title:      Tools/VSCode/src/build_vscode.scala
    Author:     Makarius

Build VSCode configuration and extension module for Isabelle.
*/

package isabelle.vscode


import isabelle._


object Build_VSCode
{
  val extension_dir = Path.explode("~~/src/Tools/VSCode/extension")


  /* grammar */

  def build_grammar(options: Options, progress: Progress = new Progress): Unit =
  {
    val logic = TextMate_Grammar.default_logic
    val keywords = Sessions.base_info(options, logic).check.base.overall_syntax.keywords

    val output_path = extension_dir + Path.explode(TextMate_Grammar.default_output(logic))
    progress.echo(output_path.implode)
    File.write_backup(output_path, TextMate_Grammar.generate(keywords))
  }


  /* extension */

  def build_extension(progress: Progress = new Progress, publish: Boolean = false): Unit =
  {
    val output_path = extension_dir + Path.explode("out")
    progress.echo(output_path.implode)

    progress.bash(
      "npm install && npm update --dev && vsce package" + (if (publish) " && vsce publish" else ""),
      cwd = extension_dir.file, echo = true).check
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_vscode", "build Isabelle/VSCode extension module",
      Scala_Project.here, args =>
    {
      var publish = false

      val getopts = Getopts("""
Usage: isabelle build_vscode

  Options are:
    -P           publish the package

Build Isabelle/VSCode extension module in directory
""" + extension_dir.expand + """

This requires npm and the vsce build and publishing tool, see also
https://code.visualstudio.com/docs/tools/vscecli
""",
        "P" -> (_ => publish = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val options = Options.init()
      val progress = new Console_Progress()

      build_grammar(options, progress)
      build_extension(progress, publish = publish)
    })
}
