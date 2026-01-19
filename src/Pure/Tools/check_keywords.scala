/*  Title:      Pure/Tools/check_keywords.scala
    Author:     Makarius

Check theory sources for conflicts with proposed keywords.
*/

package isabelle


object Check_Keywords {
  /* session theories for keyword conflicts */

  def check_keywords(
    options: Options,
    check: Set[String],
    dirs: List[Path] = Nil,
    progress: Progress,
  ): Unit = {
    progress.interrupt_handler {
      val deps = Sessions.deps(Sessions.load_structure(options, dirs = dirs), progress = progress)

      val bad =
        Par_List.maps[(Keyword.Keywords, String, Token.Pos), (Token, Position.T)](
          { case (keywords, input, start) =>
            progress.expose_interrupt()

            object Parsers extends Parse.Parsers {
              private val conflict =
                position(token("token", tok => !(tok.is_command || tok.is_keyword) && check(tok.source)))
              private val other = token("token", _ => true)
              private val item = conflict ^^ (x => Some(x)) | other ^^ (_ => None)

              val result: List[(Token, Position.T)] =
                parse_all(rep(item), Token.reader(Token.explode(keywords, input), start)) match {
                  case Success(res, _) => for (case Some(x) <- res) yield x
                  case bad => error(bad.toString)
                }
            }
            Parsers.result
          },
          List.from(
            for {
              session <- deps.sessions_structure.imports_topological_order.iterator
              base = deps(session)
              node_name <- base.proper_session_theories
            } yield {
              val path = node_name.path
              val input = File.read(path)
              val start = Token.Pos.file(File.standard_path(path))
              (base.overall_syntax.keywords, input, start)
            })
        )

      for ((tok, pos) <- bad) {
        progress.echo_warning(
          "keyword conflict: " + tok.kind.toString + " " + quote(tok.content) + Position.here(pos))
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("check_keywords", "check theory sources for conflicts with proposed keywords",
      Scala_Project.here,
      { args =>
        var dirs: List[Path] = Nil
        var options = Options.init()
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle check_keywords [OPTIONS] KEYWORDS

  Options are:
    -d DIR       include session directory
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose

  Check theory sources from all session directories for conflicts with
  newly proposed keywords (outer syntax). This reveals occurrences of
  identifiers that would have to be quoted.
""",
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
        "o:" -> (arg => options = options + arg),
        "v" -> (_ => verbose = true))

        val keywords = getopts(args)
        if (keywords.isEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)
        check_keywords(options, keywords.toSet, dirs = dirs, progress = progress)
      })
}
