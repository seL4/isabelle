/*  Title:      Tools/VSCode/src/symbols.scala
    Author:     Makarius

Generate configuration for VSCode editor extension Prettify Symbols Mode.
*/

package isabelle.vscode


import isabelle._


object Symbols
{
  /* generate configuration */

  def prettify_config: String =
    """{
  "prettifySymbolsMode.substitutions": [
      {
        "language": "isabelle",
        "revealOn": "none",
        "adjustCursorMovement": true,
        "substitutions": [""" +
          (for ((s, c) <- Symbol.codes)
           yield
            JSON.Format(
              Map("ugly" -> Library.escape_regex(s),
                "pretty" -> Library.escape_regex(Codepoint.string(c)))))
            .mkString("\n          ", ",\n          ", "") +
        """]
      }
    ]
}"""


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("vscode_symbols",
    "generate configuration for VSCode Prettify Symbols Mode", args =>
  {
    val getopts = Getopts("""
Usage: isabelle vscode_symbols

  Generate configuration for VSCode editor extension Prettify Symbols Mode.
""")

    val more_args = getopts(args)
    if (more_args.nonEmpty) getopts.usage()

    val output_path = Path.explode("isabelle-symbols.json")
    Output.writeln(output_path.implode)
    File.write_backup(output_path, prettify_config)
  })
}
