/*  Title:      Pure/Tools/update_tool.scala
    Author:     Makarius

Update theory sources based on PIDE markup.
*/

package isabelle


object Update_Tool {
  val update_elements: Markup.Elements =
    Markup.Elements(Markup.UPDATE, Markup.LANGUAGE)

  def update_xml(options: Options, xml: XML.Body): XML.Body = {
    val update_path_cartouches = options.bool("update_path_cartouches")
    val update_cite = options.bool("update_cite")
    val cite_commands = Bibtex.cite_commands(options)

    def upd(lang: Markup.Language, ts: XML.Body): XML.Body =
      ts flatMap {
        case XML.Wrapped_Elem(markup, body1, body2) =>
          val body = if (markup.name == Markup.UPDATE) body1 else body2
          upd(lang, body)
        case XML.Elem(Markup.Language(lang1), body) =>
          if (update_path_cartouches && lang1.is_path) {
            Token.read_embedded(Keyword.Keywords.empty, XML.content(body)) match {
              case Some(tok) => List(XML.Text(Symbol.cartouche(tok.content)))
              case None => upd(lang1, body)
            }
          }
          else if (update_cite && lang1.is_antiquotation) {
            List(XML.Text(Bibtex.update_cite_antiquotation(cite_commands, XML.content(body))))
          }
          else upd(lang1, body)
        case XML.Elem(_, body) => upd(lang, body)
        case XML.Text(s) if update_cite && lang.is_document =>
          List(XML.Text(Bibtex.update_cite_commands(s)))
        case t => List(t)
      }
    upd(Markup.Language.outer, xml)
  }

  def default_base_logic: String = Isabelle_System.getenv("ISABELLE_LOGIC")

  def update(options: Options,
    update_options: List[Options.Spec],
    selection: Sessions.Selection = Sessions.Selection.empty,
    base_logics: List[String] = Nil,
    progress: Progress = new Progress,
    build_heap: Boolean = false,
    clean_build: Boolean = false,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    numa_shuffling: Boolean = false,
    max_jobs: Option[Int] = None,
    fresh_build: Boolean = false,
    no_build: Boolean = false
  ): Build.Results = {
    /* excluded sessions */

    val exclude: Set[String] =
      if (base_logics.isEmpty) Set.empty
      else {
        Sessions.load_structure(options, dirs = dirs ::: select_dirs)
          .selection(Sessions.Selection(sessions = base_logics))
          .build_graph.domain
      }

    // test
    options ++ update_options

    def augment_options(name: String): List[Options.Spec] =
      if (exclude(name)) Nil else update_options


    /* build */

    val build_options = options + "build_thorough"

    val build_results =
      Build.build(build_options, progress = progress, dirs = dirs, select_dirs = select_dirs,
        selection = selection, build_heap = build_heap, clean_build = clean_build,
        numa_shuffling = numa_shuffling, max_jobs = max_jobs, fresh_build = fresh_build,
        no_build = no_build, augment_options = augment_options)

    val store = build_results.store
    val sessions_structure = build_results.deps.sessions_structure


    /* update */

    var seen_theory = Set.empty[String]

    using(Export.open_database_context(store)) { database_context =>
      for {
        session <- sessions_structure.build_topological_order
        if build_results(session).ok && !exclude(session)
      } {
        progress.echo("Updating " + session + " ...")
        val session_options = sessions_structure(session).options
        val proper_session_theory =
          build_results.deps(session).proper_session_theories.map(_.theory).toSet
        using(database_context.open_session0(session)) { session_context =>
          for {
            db <- session_context.session_db()
            theory <- store.read_theories(db, session)
            if proper_session_theory(theory) && !seen_theory(theory)
          } {
            seen_theory += theory
            val theory_context = session_context.theory(theory)
            for {
              theory_snapshot <- Build.read_theory(theory_context)
              node_name <- theory_snapshot.node_files
              snapshot = theory_snapshot.switch(node_name)
              if snapshot.node.source_wellformed
            } {
              progress.expose_interrupt()
              val xml = YXML.parse_body(YXML.string_of_body(snapshot.xml_markup(elements = update_elements)))
              val source1 = XML.content(update_xml(session_options, xml))
              if (source1 != snapshot.node.source) {
                val path = Path.explode(node_name.node)
                progress.echo("File " + quote(File.standard_path(path)))
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
        var numa_shuffling = false
        var requirements = false
        var exclude_session_groups: List[String] = Nil
        var all_sessions = false
        var build_heap = false
        var clean_build = false
        var dirs: List[Path] = Nil
        var fresh_build = false
        var session_groups: List[String] = Nil
        var max_jobs: Option[Int] = None
        var base_logics: List[String] = List(default_base_logic)
        var no_build = false
        var options = Options.init()
        var update_options: List[Options.Spec] = Nil
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
    -b           build heap images
    -c           clean build
    -d DIR       include session directory
    -f           fresh build
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs (default 1)
    -l NAMES     comma-separated list of base logics, to remain unchanged
                 (default: """ + quote(default_base_logic) + """)
    -n           no build -- take existing session build databases
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -u OPT       override "update" option for selected sessions
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Update theory sources based on PIDE markup produced by "isabelle build".
""",
        "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
        "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
        "N" -> (_ => numa_shuffling = true),
        "R" -> (_ => requirements = true),
        "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
        "a" -> (_ => all_sessions = true),
        "b" -> (_ => build_heap = true),
        "c" -> (_ => clean_build = true),
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
        "f" -> (_ => fresh_build = true),
        "g:" -> (arg => session_groups = session_groups ::: List(arg)),
        "j:" -> (arg => max_jobs = Some(Value.Nat.parse(arg))),
        "l:" -> (arg => base_logics = space_explode(',', arg)),
        "n" -> (_ => no_build = true),
        "o:" -> (arg => options = options + arg),
        "u:" -> (arg => update_options = update_options ::: List(Options.Spec("update_" + arg))),
        "v" -> (_ => verbose = true),
        "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

        val sessions = getopts(args)

        val progress = new Console_Progress(verbose = verbose)

        val results =
          progress.interrupt_handler {
            update(options, update_options,
              selection = Sessions.Selection(
                requirements = requirements,
                all_sessions = all_sessions,
                base_sessions = base_sessions,
                exclude_session_groups = exclude_session_groups,
                exclude_sessions = exclude_sessions,
                session_groups = session_groups,
                sessions = sessions),
              base_logics = base_logics,
              progress = progress,
              build_heap = build_heap,
              clean_build = clean_build,
              dirs = dirs,
              select_dirs = select_dirs,
              numa_shuffling = Host.numa_check(progress, numa_shuffling),
              max_jobs = max_jobs,
              fresh_build = fresh_build,
              no_build = no_build)
          }

        sys.exit(results.rc)
      })
}
