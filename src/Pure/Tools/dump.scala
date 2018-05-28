/*  Title:      Pure/Tools/dump.scala
    Author:     Makarius

Dump build database produced by PIDE session.
*/

package isabelle


object Dump
{
  def dump(options: Options, logic: String,
    consume: Thy_Resources.Theories_Result => Unit = _ => (),
    progress: Progress = No_Progress,
    log: Logger = No_Logger,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    verbose: Boolean = false,
    system_mode: Boolean = false,
    selection: Sessions.Selection = Sessions.Selection.empty): Process_Result =
  {
    if (Build.build_logic(options, logic, progress = progress, dirs = dirs,
      system_mode = system_mode) != 0) error(logic + " FAILED")

    val dump_options = options.int.update("completion_limit", 0).bool.update("ML_statistics", false)

    val deps =
      Sessions.load_structure(dump_options, dirs = dirs, select_dirs = select_dirs).
        selection_deps(selection)

    val session =
      Thy_Resources.start_session(dump_options, logic, session_dirs = dirs,
        include_sessions = deps.sessions_structure.imports_topological_order,
        progress = progress, log = log)

    val theories = deps.all_known.theory_graph.topological_order.map(_.theory)
    val theories_result = session.use_theories(theories, progress = progress)

    try { consume(theories_result) }
    catch { case exn: Throwable => session.stop (); throw exn }

    session.stop()
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("dump", "dump build database produced by PIDE session.", args =>
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
      var system_mode = false
      var verbose = false
      var exclude_sessions: List[String] = Nil

      val getopts = Getopts("""
Usage: isabelle dump [OPTIONS] [SESSIONS ...]

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
    -s           system build mode for logic image
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Dump build database (PIDE markup etc.) based on dynamic session.""",
      "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
      "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
      "R" -> (_ => requirements = true),
      "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
      "a" -> (_ => all_sessions = true),
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "l:" -> (arg => logic = arg),
      "g:" -> (arg => session_groups = session_groups ::: List(arg)),
      "o:" -> (arg => options = options + arg),
      "s" -> (_ => system_mode = true),
      "v" -> (_ => verbose = true),
      "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

      val sessions = getopts(args)

      val progress = new Console_Progress(verbose = verbose)

      def consume(theories_result: Thy_Resources.Theories_Result)
      {
        // FIXME
        for ((node, _) <- theories_result.nodes) progress.echo(node.toString)
      }

      val result =
        dump(options, logic,
          consume = consume _,
          progress = progress,
          dirs = dirs,
          select_dirs = select_dirs,
          verbose = verbose,
          selection = Sessions.Selection(
            requirements = requirements,
            all_sessions = all_sessions,
            base_sessions = base_sessions,
            exclude_session_groups = exclude_session_groups,
            exclude_sessions = exclude_sessions,
            session_groups = session_groups,
            sessions = sessions))

      progress.echo(result.timing.message_resources)

      sys.exit(result.rc)
    })
}
