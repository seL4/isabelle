/*  Title:      Tools/VSCode/src/grammar.scala
    Author:     Makarius

Generate static TextMate grammar for VSCode editor.
*/

package isabelle.vscode


import isabelle._


object Grammar
{
  /* generate grammar */

  lazy val default_logic = Isabelle_System.getenv("ISABELLE_LOGIC")

  def default_output(logic: String = ""): String =
    if (logic == "" || logic == default_logic) "isabelle-grammar.json"
    else "isabelle-" + logic + "-grammar.json"

  def generate(keywords: Keyword.Keywords): JSON.S =
  {
    val (minor_keywords, operators) =
      keywords.minor.iterator.toList.partition(Symbol.is_ascii_identifier)

    def major_keywords(pred: String => Boolean): List[String] =
      (for {
        k <- keywords.major.iterator
        kind <- keywords.kinds.get(k)
        if pred(kind)
      } yield k).toList

    val keywords1 =
      major_keywords(k => k != Keyword.THY_END && k != Keyword.PRF_ASM && k != Keyword.PRF_ASM_GOAL)
    val keywords2 = minor_keywords ::: major_keywords(Set(Keyword.THY_END))
    val keywords3 = major_keywords(Set(Keyword.PRF_ASM, Keyword.PRF_ASM_GOAL))


    def grouped_names(as: List[String]): String =
      JSON.Format("\\b(" + as.sorted.map(Library.escape_regex).mkString("|") + ")\\b")

    """{
  "name": "Isabelle",
  "scopeName": "source.isabelle",
  "fileTypes": ["thy"],
  "uuid": """ + JSON.Format(UUID.random_string()) + """,
  "repository": {
    "comment": {
      "patterns": [
        {
          "name": "comment.block.isabelle",
          "begin": "\\(\\*",
          "patterns": [{ "include": "#comment" }],
          "end": "\\*\\)"
        }
      ]
    },
    "cartouche": {
      "patterns": [
        {
          "name": "string.quoted.other.multiline.isabelle",
          "begin": "(?:\\\\<open>|‹)",
          "patterns": [{ "include": "#cartouche" }],
          "end": "(?:\\\\<close>|›)"
        }
      ]
    }
  },
  "patterns": [
    {
      "include": "#comment"
    },
    {
      "include": "#cartouche"
    },
    {
      "name": "keyword.control.isabelle",
      "match": """ + grouped_names(keywords1) + """
    },
    {
      "name": "keyword.other.unit.isabelle",
      "match": """ + grouped_names(keywords2) + """
    },
    {
      "name": "keyword.operator.isabelle",
      "match": """ + grouped_names(operators) + """
    },
    {
      "name": "entity.name.type.isabelle",
      "match": """ + grouped_names(keywords3) + """
    },
    {
      "name": "constant.numeric.isabelle",
      "match": "\\b\\d*\\.?\\d+\\b"
    },
    {
      "name": "string.quoted.double.isabelle",
      "begin": "\"",
      "patterns": [
        {
          "name": "constant.character.escape.isabelle",
          "match": """ + JSON.Format("""\\[\"]|\\\d\d\d""") + """
        }
      ],
      "end": "\""
    },
    {
      "name": "string.quoted.backtick.isabelle",
      "begin": "`",
      "patterns": [
        {
          "name": "constant.character.escape.isabelle",
          "match": """ + JSON.Format("""\\[\`]|\\\d\d\d""") + """
        }
      ],
      "end": "`"
    },
    {
      "name": "string.quoted.verbatim.isabelle",
      "begin": """ + JSON.Format("""\{\*""") + """,
      "patterns": [
        { "match": """ + JSON.Format("""[^*]+|\*(?!\})""") + """ }
      ],
      "end": """ + JSON.Format("""\*\}""") + """
    }
  ]
}
"""
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("vscode_grammar",
    "generate static TextMate grammar for VSCode editor", Scala_Project.here, args =>
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

    val keywords =
      Sessions.base_info(Options.init(), logic, dirs = dirs).check.base.overall_syntax.keywords
    val output_path = output getOrElse Path.explode(default_output(logic))

    Output.writeln(output_path.implode)
    File.write_backup(output_path, generate(keywords))
  })
}
