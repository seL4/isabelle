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

  def build_extension(progress: Progress = new Progress, install: Boolean = false): Unit =
  {
    val output_path = extension_dir + Path.explode("out")
    Isabelle_System.rm_tree(output_path)
    Isabelle_System.make_directory(output_path)
    progress.echo(output_path.implode)

    val result =
      progress.bash("npm install && npm update --dev && vsce package",
        cwd = extension_dir.file, echo = true).check

    if (install) {
      val Pattern = """.*Packaged:.*(Isabelle-.*\.vsix).*""".r
      val vsix_name =
        result.out_lines.collectFirst({ case Pattern(name) => name }) getOrElse
          error("Cannot install extension: failed to guess resulting .vsix file name")
      progress.bash("isabelle vscode --install-extension " +
        File.bash_platform_path(extension_dir + Path.basic(vsix_name)))
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_vscode", "build Isabelle/VSCode extension module",
      Scala_Project.here, args =>
    {
      var install = false

      val getopts = Getopts("""
Usage: isabelle build_vscode

  Options are:
    -I           install resulting extension

Build Isabelle/VSCode extension module in directory
""" + extension_dir.expand + """

This requires node.js/npm and the vsce build tool.
""",
        "I" -> (_ => install = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val options = Options.init()
      val progress = new Console_Progress()

      build_grammar(options, progress)
      build_extension(progress, install = install)
    })
}
