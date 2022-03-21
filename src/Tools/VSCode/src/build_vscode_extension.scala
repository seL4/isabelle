/*  Title:      Tools/VSCode/src/build_vscode_extension.scala
    Author:     Makarius

Build the Isabelle/VSCode extension.
*/

package isabelle.vscode


import isabelle._


object Build_VSCode
{
  val extension_dir: Path = Path.explode("$ISABELLE_VSCODE_HOME/extension")


  /* build grammar */

  def default_logic: String = Isabelle_System.getenv("ISABELLE_LOGIC")

  def build_grammar(options: Options,
    logic: String = default_logic,
    dirs: List[Path] = Nil,
    progress: Progress = new Progress): Unit =
  {
    val keywords =
      Sessions.base_info(options, logic, dirs = dirs).check.base.overall_syntax.keywords

    val output_path = extension_dir + Path.explode("isabelle-grammar.json")
    progress.echo(output_path.expand.implode)

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

    File.write_backup(output_path, """{
  "name": "Isabelle",
  "scopeName": "source.isabelle",
  "fileTypes": ["thy"],
  "uuid": """ + JSON.Format(UUID.random().toString) + """,
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
""")
  }


  /* extension */

  def uninstall_extension(progress: Progress = new Progress): Unit =
    progress.bash("isabelle vscode --uninstall-extension Isabelle.isabelle").check

  def install_extension(vsix_path: Path, progress: Progress = new Progress): Unit =
    progress.bash("isabelle vscode --install-extension " +
      File.bash_platform_path(vsix_path)).check

  def build_extension(progress: Progress = new Progress): Path =
  {
    Isabelle_System.require_command("node")
    Isabelle_System.require_command("yarn")
    Isabelle_System.require_command("vsce")

    val output_path = extension_dir + Path.explode("out")
    Isabelle_System.rm_tree(output_path)
    Isabelle_System.make_directory(output_path)
    progress.echo(output_path.expand.implode)

    val result =
      progress.bash("yarn && vsce package", cwd = extension_dir.file, echo = true).check

    val Pattern = """.*Packaged:.*(isabelle-.*\.vsix).*""".r
    result.out_lines.collectFirst(
      { case Pattern(vsix_name) => extension_dir + Path.basic(vsix_name) })
      .getOrElse(error("Failed to guess resulting .vsix file name"))
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_vscode_extension", "build Isabelle/VSCode extension module",
      Scala_Project.here, args =>
    {
      var dirs: List[Path] = Nil
      var logic = default_logic
      var install = false
      var uninstall = false

      val getopts = Getopts("""
Usage: isabelle build_vscode_extension

  Options are:
    -I           install resulting extension
    -U           uninstall extension (no build)
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(default_logic) + """)

Build Isabelle/VSCode extension module in directory
""" + extension_dir.expand + """
""",
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
        "l:" -> (arg => logic = arg),
        "I" -> (_ => install = true),
        "U" -> (_ => uninstall = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val options = Options.init()
      val progress = new Console_Progress()

      if (uninstall) {
        uninstall_extension(progress = progress)
      }
      else {
        build_grammar(options, logic = logic, dirs = dirs, progress = progress)
        val path = build_extension(progress = progress)
        if (install) install_extension(path, progress = progress)
      }
    })
}
