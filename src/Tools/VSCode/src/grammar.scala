/*  Title:      Tools/VSCode/src/grammar.scala
    Author:     Makarius

Generate static TextMate grammar for VSCode editor.
*/

package isabelle.vscode


import isabelle._


object Grammar
{
  /* generate grammar */

  private lazy val default_logic = Isabelle_System.getenv("ISABELLE_LOGIC")

  private def default_output(logic: String = ""): String =
    if (logic == default_logic) "isabelle-grammar.json"
    else "isabelle-" + logic + "-grammar.json"

  def generate(
    options: Options,
    session_dirs: List[Path] = Nil,
    session_name: String = default_logic,
    output: Path = Path.explode(default_output()))
  {
    val keywords = Build.outer_syntax(options, session_dirs, session_name).keywords

    val (minor_keywords, operators) =
      keywords.minor.iterator.toList.partition(Symbol.is_ascii_identifier(_))

    def major_keywords(pred: String => Boolean): List[String] =
      (for {
        k <- keywords.major.iterator
        kind <- keywords.kinds.get(k)
        if pred(kind)
      } yield k).toList

    val keywords1 =
      major_keywords(k => k != Keyword.THY_END && k != Keyword.PRF_ASM && k != Keyword.PRF_ASM_GOAL)
    val keywords2 = major_keywords(Set(Keyword.THY_END))
    val keywords3 = major_keywords(Set(Keyword.PRF_ASM, Keyword.PRF_ASM_GOAL))


    def quote_name(a: String): String =
      if (Symbol.is_ascii_identifier(a)) a else "\\Q" + a + "\\E"

    def grouped_names(as: List[String]): String =
      JSON.Format("\\b(" + as.sorted.map(quote_name(_)).mkString("|") + ")\\b")

    File.write(output, """{
  "name": "Isabelle",
  "scopeName": "source.isabelle",
  "fileTypes": ["thy"],
  "uuid": "fb16e918-d05b-11e6-918e-2bb94aa2c605",
  "repository": {
    "comments": {
      "patterns": [
        {
          "name": "comment.block.isabelle",
          "begin": "\\(\\*",
          "beginCaptures": {
            "0": { "name": "punctuation.definition.comment.begin.isabelle" }
          },
          "patterns": [{ "include": "#comments" }],
          "end": "\\*\\)",
          "endCaptures": {
            "0": { "name": "punctuation.definition.comment.end.isabelle" }
          }
        }
      ]
    }
  },
  "patterns": [
    {
      "include": "#comments"
    },
    {
      "name": "keyword.control.isabelle",
      "match": """ + grouped_names(keywords1) + """
    },
    {
      "name": "keyword.other.isabelle",
      "match": """ + grouped_names(keywords2) + """
    },
    {
      "name": "keyword.operator.isabelle",
      "match": """ + grouped_names(operators) + """
    },
    {
      "name": "constant.language.isabelle",
      "match": """ + grouped_names(keywords3) + """
    },
    {
      "match": "\\b\\d*\\.?\\d+\\b",
      "name": "constant.numeric.isabelle"
    },
    {
      "name": "string.quoted.double.isabelle",
      "begin": "\"",
      "beginCaptures": {
        "0": { "name": "punctuation.definition.string.begin.isabelle" }
      },
      "patterns": [
        {
          "match": "\\\\.",
          "name": "constant.character.escape.isabelle"
        }
      ],
      "end": "\"",
      "endCaptures": {
        "0": { "name": "punctuation.definition.string.end.isabelle" }
      }
    }
  ]
}
""")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("vscode_grammar",
    "generate static TextMate grammar for VSCode editor", args =>
  {
    var dirs: List[Path] = Nil
    var logic = default_logic
    var output: Option[Path] = None

    val getopts = Getopts("""
Usage: isabelle vscode_grammar [OPTIONS]

  Options are:
    -d DIR       include session directory
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(default_logic) + """)
    -o FILE      output file name (default """ + default_output() + """)

  Generate static TextMate grammar for VSCode editor.
""",
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "l:" -> (arg => logic = arg),
      "o:" -> (arg => output = Some(Path.explode(arg))))

    val more_args = getopts(args)
    if (more_args.nonEmpty) getopts.usage()

    val output_path = output getOrElse Path.explode(default_output(logic))
    Output.writeln(output_path.implode)

    generate(Options.init(), dirs, logic, output_path)
  })
}
