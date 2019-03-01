/*  Title:      Pure/Tools/update.scala
    Author:     Makarius

Update theory sources based on PIDE markup.
*/

package isabelle


object Update
{
  def update(options: Options, logic: String,
    progress: Progress = No_Progress,
    log: Logger = No_Logger,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    selection: Sessions.Selection = Sessions.Selection.empty)
  {
    Build.build_logic(options, logic, build_heap = true, progress = progress,
      dirs = dirs ::: select_dirs, strict = true)

    val dump_options = Dump.make_options(options)

    val deps =
      Dump.dependencies(dump_options, progress = progress,
        dirs = dirs, select_dirs = select_dirs, selection = selection)._1

    val resources =
      Headless.Resources.make(dump_options, logic, progress = progress, log = log,
        session_dirs = dirs ::: select_dirs,
        include_sessions = deps.sessions_structure.imports_topological_order)

    val path_cartouches = dump_options.bool("update_path_cartouches")

    def update_xml(xml: XML.Body): XML.Body =
      xml flatMap {
        case XML.Wrapped_Elem(markup, body1, body2) =>
          if (markup.name == Markup.UPDATE) update_xml(body1) else update_xml(body2)
        case XML.Elem(Markup.Language(Markup.Language.PATH, _, _, _), body)
        if path_cartouches =>
          Token.read_embedded(Keyword.Keywords.empty, XML.content(body)) match {
            case Some(tok) => List(XML.Text(Symbol.cartouche(tok.content)))
            case None => update_xml(body)
          }
        case XML.Elem(_, body) => update_xml(body)
        case t => List(t)
      }

    Dump.session(deps, resources, progress = progress,
      process_theory =
        (deps: Sessions.Deps, snapshot: Document.Snapshot, status: Document_Status.Node_Status) =>
        {
          progress.echo("Processing theory " + snapshot.node_name + " ...")

          for ((node_name, node) <- snapshot.nodes) {
            val xml =
              snapshot.state.markup_to_XML(snapshot.version, node_name,
                Text.Range.full, Markup.Elements(Markup.UPDATE, Markup.LANGUAGE))

            val source1 = Symbol.encode(XML.content(update_xml(xml)))
            if (source1 != Symbol.encode(node.source)) {
              progress.echo("Updating " + node_name.path)
              File.write(node_name.path, source1)
            }
          }
        })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("update", "update theory sources based on PIDE markup", args =>
    {
      var base_sessions: List[String] = Nil
      var select_dirs: List[Path] = Nil
      var requirements = false
      var exclude_session_groups: List[String] = Nil
      var all_sessions = false
      var dirs: List[Path] = Nil
      var session_groups: List[String] = Nil
      var logic = Isabelle_System.getenv("ISABELLE_LOGIC")
      var options = Options.init()
      var verbose = false
      var exclude_sessions: List[String] = Nil

      val getopts = Getopts("""
Usage: isabelle update [OPTIONS] [SESSIONS ...]

  Options are:
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -R           operate on requirements of selected sessions
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -d DIR       include session directory
    -g NAME      select session group NAME
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(logic) + """)
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
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "g:" -> (arg => session_groups = session_groups ::: List(arg)),
      "l:" -> (arg => logic = arg),
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
