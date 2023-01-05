/*  Title:      Pure/Tools/update.scala
    Author:     Makarius

Update theory sources based on PIDE markup.
*/

package isabelle


object Update {
  def update(options: Options,
    base_logics: List[String] = Nil,
    progress: Progress = new Progress,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    selection: Sessions.Selection = Sessions.Selection.empty
  ): Build.Results = {
    /* excluded sessions */

    val exclude: Set[String] =
      if (base_logics.isEmpty) Set.empty
      else {
        val sessions =
          Sessions.load_structure(options, dirs = dirs, select_dirs = select_dirs)
            .selection(selection)

        for (name <- base_logics if !sessions.defined(name)) {
          error("Base logic " + quote(name) + " outside of session selection")
        }

        sessions.build_requirements(base_logics).toSet
      }


    /* build */

    val build_results =
      Build.build(options, progress = progress, dirs = dirs, select_dirs = select_dirs,
        selection = selection)

    if (!build_results.ok) error("Build failed")

    val store = build_results.store
    val sessions_structure = build_results.deps.sessions_structure


    /* update */

    val path_cartouches = options.bool("update_path_cartouches")

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

    var seen_theory = Set.empty[String]

    using(Export.open_database_context(store)) { database_context =>
      for (session <- sessions_structure.build_topological_order if !exclude(session)) {
        using(database_context.open_session0(session)) { session_context =>
          for {
            db <- session_context.session_db()
            theory <- store.read_theories(db, session)
            if !seen_theory(theory)
          } {
            seen_theory += theory
            val theory_context = session_context.theory(theory)
            for {
              theory_snapshot <- Build_Job.read_theory(theory_context)
              node_name <- theory_snapshot.node_files
              snapshot = theory_snapshot.switch(node_name)
              if snapshot.node.is_wellformed_text
            } {
              progress.expose_interrupt()
              val source1 =
                XML.content(update_xml(
                  snapshot.xml_markup(elements = Markup.Elements(Markup.UPDATE, Markup.LANGUAGE))))
              if (source1 != snapshot.node.source) {
                val path = Path.explode(node_name.node)
                progress.echo("Updating " + quote(File.standard_path(path)))
                File.write(path, source1)
              }
            }
          }
        }
      }
    }

    build_results
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("update", "update theory sources based on PIDE markup", Scala_Project.here,
      { args =>
        var base_sessions: List[String] = Nil
        var select_dirs: List[Path] = Nil
        var requirements = false
        var exclude_session_groups: List[String] = Nil
        var all_sessions = false
        var dirs: List[Path] = Nil
        var session_groups: List[String] = Nil
        var base_logics: List[String] = Nil
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
    -b NAME      additional base logic
    -d DIR       include session directory
    -g NAME      select session group NAME
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -u OPT       override "update" option: shortcut for "-o update_OPT"
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Update theory sources based on PIDE markup.
""",
        "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
        "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
        "R" -> (_ => requirements = true),
        "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
        "a" -> (_ => all_sessions = true),
        "b:" -> (arg => base_logics ::= arg),
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
        "g:" -> (arg => session_groups = session_groups ::: List(arg)),
        "o:" -> (arg => options = options + arg),
        "u:" -> (arg => options = options + ("update_" + arg)),
        "v" -> (_ => verbose = true),
        "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

        val sessions = getopts(args)

        val progress = new Console_Progress(verbose = verbose)

        val results =
          progress.interrupt_handler {
            update(options,
              base_logics = base_logics,
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

        sys.exit(results.rc)
      })
}
