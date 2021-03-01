/*  Title:      Pure/Tools/update.scala
    Author:     Makarius

Update theory sources based on PIDE markup.
*/

package isabelle


object Update
{
  def update(options: Options, logic: String,
    progress: Progress = new Progress,
    log: Logger = No_Logger,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    selection: Sessions.Selection = Sessions.Selection.empty): Unit =
  {
    val context =
      Dump.Context(options, progress = progress, dirs = dirs, select_dirs = select_dirs,
        selection = selection, skip_base = true)

    context.build_logic(logic)

    val path_cartouches = context.options.bool("update_path_cartouches")

    def update_xml(xml: XML.Body): XML.Body =
      xml flatMap {
        case XML.Wrapped_Elem(markup, body1, body2) =>
          if (markup.name == Markup.UPDATE) update_xml(body1) else update_xml(body2)
        case XML.Elem(Markup.Language.Path(_), body)
        if path_cartouches =>
          Token.read_embedded(Keyword.Keywords.empty, XML.content(body)) match {
            case Some(tok) => List(XML.Text(Symbol.cartouche(tok.content)))
            case None => update_xml(body)
          }
        case XML.Elem(_, body) => update_xml(body)
        case t => List(t)
      }

    context.sessions(logic, log = log).foreach(_.process((args: Dump.Args) =>
      {
        progress.echo("Processing theory " + args.print_node + " ...")

        val snapshot = args.snapshot
        for (node_name <- snapshot.node_files) {
          val node = snapshot.get_node(node_name)
          val xml =
            snapshot.state.xml_markup(snapshot.version, node_name,
              elements = Markup.Elements(Markup.UPDATE, Markup.LANGUAGE))

          val source1 = Symbol.encode(XML.content(update_xml(xml)))
          if (source1 != Symbol.encode(node.source)) {
            progress.echo("Updating " + node_name.path)
            File.write(node_name.path, source1)
          }
        }
      }))

    context.check_errors
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("update", "update theory sources based on PIDE markup", Scala_Project.here,
      args =>
    {
      var base_sessions: List[String] = Nil
      var select_dirs: List[Path] = Nil
      var requirements = false
      var exclude_session_groups: List[String] = Nil
      var all_sessions = false
      var dirs: List[Path] = Nil
      var session_groups: List[String] = Nil
      var logic = Dump.default_logic
      var options = Options.init()
      var verbose = false
      var exclude_sessions: List[String] = Nil

      val getopts = Getopts("""
Usage: isabelle update [OPTIONS] [SESSIONS ...]

  Options are:
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -R           refer to requirements of selected sessions
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -b NAME      base logic image (default """ + isabelle.quote(Dump.default_logic) + """)
    -d DIR       include session directory
    -g NAME      select session group NAME
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -u OPT       overide update option: shortcut for "-o update_OPT"
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Update theory sources based on PIDE markup.
""",
      "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
      "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
      "R" -> (_ => requirements = true),
      "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
      "a" -> (_ => all_sessions = true),
      "b:" -> (arg => logic = arg),
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "g:" -> (arg => session_groups = session_groups ::: List(arg)),
      "o:" -> (arg => options = options + arg),
      "u:" -> (arg => options = options + ("update_" + arg)),
      "v" -> (_ => verbose = true),
      "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

      val sessions = getopts(args)

      val progress = new Console_Progress(verbose = verbose)

      progress.interrupt_handler {
        update(options, logic,
          progress = progress,
          dirs = dirs,
          select_dirs = select_dirs,
          selection = Sessions.Selection(
            requirements = requirements,
            all_sessions = all_sessions,
            base_sessions = base_sessions,
            exclude_session_groups = exclude_session_groups,
            exclude_sessions = exclude_sessions,
            session_groups = session_groups,
            sessions = sessions))
      }
    })
}
