/*  Title:      Tools/VSCode/src/build_vscode_extension.scala
    Author:     Makarius

Build the Isabelle/VSCode extension.
*/

package isabelle.vscode


import isabelle._


object Build_VSCode
{
  /* build grammar */

  def default_logic: String = Isabelle_System.getenv("ISABELLE_LOGIC")

  def build_grammar(options: Options, build_dir: Path,
    logic: String = default_logic,
    dirs: List[Path] = Nil,
    progress: Progress = new Progress): Unit =
  {
    val keywords =
      Sessions.base_info(options, logic, dirs = dirs).check.base.overall_syntax.keywords

    val output_path = build_dir + Path.explode("isabelle-grammar.json")
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

  lazy val extension_dir = Path.explode("$ISABELLE_VSCODE_HOME/extension")

  def uninstall_extension(progress: Progress = new Progress): Unit =
    VSCode_Main.run_cli(
      List("--uninstall-extension", "Isabelle.isabelle"), progress = progress).check

  def install_extension(vsix: File.Content, progress: Progress = new Progress): Unit =
  {
    Isabelle_System.with_tmp_dir("tmp")(tmp_dir =>
    {
      vsix.write(tmp_dir)
      VSCode_Main.run_cli(
        List("--install-extension", File.platform_path(tmp_dir + vsix.path)), progress = progress).check
    })
  }

  def build_extension(options: Options,
    logic: String = default_logic,
    dirs: List[Path] = Nil,
    progress: Progress = new Progress): File.Content =
  {
    Isabelle_System.require_command("node")
    Isabelle_System.require_command("yarn")
    Isabelle_System.require_command("vsce")

    Isabelle_System.with_tmp_dir("build")(build_dir =>
    {
      for {
        line <- split_lines(File.read(extension_dir + Path.explode("MANIFEST")))
        if line.nonEmpty
      } {
        val path = Path.explode(line)
        Isabelle_System.copy_file(extension_dir + path,
          Isabelle_System.make_directory(build_dir + path.dir))
      }

      build_grammar(options, build_dir, logic = logic, dirs = dirs, progress = progress)

      val result =
        progress.bash("yarn && vsce package", cwd = build_dir.file, echo = true).check
      val Pattern = """.*Packaged:.*(isabelle-.*\.vsix).*""".r
      val path =
        result.out_lines.collectFirst({ case Pattern(name) => Path.explode(name) })
          .getOrElse(error("Failed to guess resulting .vsix file name"))
      File.Content(path, Bytes.read(build_dir + path))
    })
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
    -d DIR       include session directory
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(default_logic) + """)

Build Isabelle/VSCode extension module (vsix).
""",
        "I" -> (_ => install = true),
        "U" -> (_ => uninstall = true),
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
        "l:" -> (arg => logic = arg))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val options = Options.init()
      val progress = new Console_Progress()

      if (uninstall) uninstall_extension(progress = progress)
      else {
        val vsix = build_extension(options, logic = logic, dirs = dirs, progress = progress)
        vsix.write(extension_dir)
        if (install) install_extension(vsix, progress = progress)
      }
    })
}
