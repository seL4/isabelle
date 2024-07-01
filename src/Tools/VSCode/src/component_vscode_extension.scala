/*  Title:      Tools/VSCode/src/component_vscode_extension.scala
    Author:     Makarius

Build the Isabelle/VSCode extension as component.
*/

package isabelle.vscode


import isabelle._


object Component_VSCode {
  /* build grammar */

  def default_logic: String = Isabelle_System.getenv("ISABELLE_LOGIC")

  def build_grammar(options: Options, build_dir: Path,
    logic: String = default_logic,
    dirs: List[Path] = Nil,
    progress: Progress = new Progress
  ): Unit = {
    val keywords =
      Sessions.background(options, logic, dirs = dirs).check_errors.base.overall_syntax.keywords

    val output_path = build_dir + Path.explode("isabelle-grammar.json")
    progress.echo(File.standard_path(output_path))

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
""")
  }
  

  private def options_json(options: Options): String = {
    val relevant_options = Set(
      "editor_output_state",
      "auto_time_start",
      "auto_time_limit",
      "auto_nitpick",
      "auto_sledgehammer",
      "auto_methods",
      "auto_quickcheck",
      "auto_solve_direct",
      "sledgehammer_provers",
      "sledgehammer_timeout",
    )
    
    options.iterator.filter(
      opt => opt.for_tag(Options.TAG_VSCODE) || opt.for_content || relevant_options.contains(opt.name)
    ).map(opt => {
      val (enum_values, enum_descriptions) = opt.typ match {
        case Options.Bool => (
          Some(List("", "true", "false")),
          Some(List("Use System Preference.", "Enable.", "Disable."))
        )
        case _ => (None, None)
      }

      val default = opt.name match {
        case "vscode_unicode_symbols_output" => "true"
        case "vscode_unicode_symbols_edits" => "false"
        case "vscode_pide_extensions" => "true"
        case "vscode_html_output" => "true"
        case _ => ""
      }

      quote("isabelle.options." + opt.name) + ": " + JSON.Format(
        JSON.Object(
          "type" -> "string",
          "default" -> default,
          "description" -> opt.description,
        ) ++ JSON.optional("enum" -> enum_values) ++ JSON.optional("enumDescriptions" -> enum_descriptions)
      ) + ","
    }).mkString
  }


  /* build extension */

  def build_extension(options: Options,
    target_dir: Path = Path.current,
    logic: String = default_logic,
    dirs: List[Path] = Nil,
    progress: Progress = new Progress
  ): Unit = {
    Isabelle_System.require_command("node")
    Isabelle_System.require_command("yarn")
    Isabelle_System.require_command("vsce")


    /* component */

    val component_name = "vscode_extension-" + Date.Format.alt_date(Date.now())
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)


    /* build */

    val vsix_name =
      Isabelle_System.with_tmp_dir("build") { build_dir =>
        val manifest_text = File.read(VSCode_Main.extension_dir + VSCode_Main.MANIFEST)
        val manifest_entries = split_lines(manifest_text).filter(_.nonEmpty)
        for (name <- manifest_entries) {
          val path = Path.explode(name)
          Isabelle_System.copy_file(VSCode_Main.extension_dir + path,
            Isabelle_System.make_directory(build_dir + path.dir))
        }

        for (entry <- Isabelle_Fonts.fonts()) {
          Isabelle_System.copy_file(entry.path, Isabelle_System.make_directory(build_dir + Path.basic("fonts")))
        }
        val manifest_text2 =
          manifest_text + cat_lines(Isabelle_Fonts.fonts().map(e => "fonts/" + e.path.file_name))
        val manifest_entries2 = split_lines(manifest_text2).filter(_.nonEmpty)

        val manifest_shasum: SHA1.Shasum = {
          val a = SHA1.shasum_meta_info(SHA1.digest(manifest_text2))
          val bs =
            for (name <- manifest_entries2)
              yield SHA1.shasum(SHA1.digest(build_dir + Path.explode(name)), name)
          SHA1.flat_shasum(a :: bs)
        }
        File.write(build_dir + VSCode_Main.MANIFEST.shasum, manifest_shasum.toString)


        /* options */

        val opt_json = options_json(options)
        val package_path = build_dir + Path.basic("package.json")
        val package_body = File.read(package_path).replace("/*options*/", opt_json)
        File.write(package_path, package_body)


        build_grammar(options, build_dir, logic = logic, dirs = dirs, progress = progress)

        val result =
          progress.bash("yarn && vsce package", cwd = build_dir, echo = true).check
        val Pattern = """.*Packaged:.*(isabelle-.*\.vsix).*""".r
        val vsix_name =
          result.out_lines.collectFirst({ case Pattern(name) => name })
            .getOrElse(error("Failed to guess resulting .vsix file name"))

        Isabelle_System.copy_file(build_dir + Path.basic(vsix_name), component_dir.path)
        vsix_name
      }


    /* settings */

    component_dir.write_settings("""
ISABELLE_VSCODE_VSIX="$COMPONENT/""" + vsix_name + "\"\n")


    /* README */

    File.write(component_dir.README,
      """This the Isabelle/VSCode extension as VSIX package

It has been produced from the sources in $ISABELLE_HOME/src/Tools/extension/.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_vscode_extension", "build Isabelle/VSCode extension module",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var dirs: List[Path] = Nil
        var logic = default_logic

        val getopts = Getopts("""
Usage: isabelle component_vscode_extension

  Options are:
    -D DIR       target directory (default ".")
    -d DIR       include session directory
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(default_logic) + """)

Build the Isabelle/VSCode extension as component, for inclusion into the
local VSCodium configuration.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
          "l:" -> (arg => logic = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val options = Options.init()
        val progress = new Console_Progress()

        build_extension(options, target_dir = target_dir, logic = logic, dirs = dirs,
          progress = progress)
      })
}
