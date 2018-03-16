/*  Title:      Pure/Tools/server_commands.scala
    Author:     Makarius

Miscellaneous Isabelle server commands.
*/

package isabelle


object Server_Commands
{
  def default_preferences: String = Options.read_prefs()
  def default_qualifier: String = Sessions.DRAFT

  def unapply_name_pos(json: JSON.T): Option[(String, Position.T)] =
    json match {
      case JSON.Value.String(name) => Some((name, Position.none))
      case JSON.Object(map) if map.keySet == Set("name", "pos") =>
      (map("name"), map("pos")) match {
        case (JSON.Value.String(name), Position.JSON(pos)) => Some((name, pos))
        case _ => None
      }
      case _ => None
    }

  object Session_Build
  {
    sealed case class Args(
      session: String,
      preferences: String = default_preferences,
      options: List[String] = Nil,
      dirs: List[String] = Nil,
      ancestor_session: String = "",
      all_known: Boolean = false,
      focus_session: Boolean = false,
      required_session: Boolean = false,
      system_mode: Boolean = false,
      verbose: Boolean = false)

    def unapply(json: JSON.T): Option[Args] =
      for {
        session <- JSON.string(json, "session")
        preferences <- JSON.string_default(json, "preferences", default_preferences)
        options <- JSON.list_default(json, "options", JSON.Value.String.unapply _)
        dirs <- JSON.list_default(json, "dirs", JSON.Value.String.unapply _)
        ancestor_session <- JSON.string_default(json, "ancestor_session")
        all_known <- JSON.bool_default(json, "all_known")
        focus_session <- JSON.bool_default(json, "focus_session")
        required_session <- JSON.bool_default(json, "required_session")
        system_mode <- JSON.bool_default(json, "system_mode")
        verbose <- JSON.bool_default(json, "verbose")
      }
      yield {
        Args(session, preferences = preferences, options = options, dirs = dirs,
          ancestor_session = ancestor_session, all_known = all_known, focus_session = focus_session,
          required_session = required_session, system_mode = system_mode, verbose = verbose)
      }

    def command(progress: Progress, args: Args)
      : (JSON.Object.T, Build.Results, Sessions.Base_Info) =
    {
      val options = Options.init(prefs = args.preferences, opts = args.options)
      val dirs = args.dirs.map(Path.explode(_))

      val base_info =
        Sessions.base_info(options,
          args.session,
          progress = progress,
          dirs = dirs,
          ancestor_session = proper_string(args.ancestor_session),
          all_known = args.all_known,
          focus_session = args.focus_session,
          required_session = args.required_session)
      val base = base_info.check_base

      val results =
        Build.build(options,
          progress = progress,
          build_heap = true,
          system_mode = args.system_mode,
          dirs = dirs,
          infos = base_info.infos,
          verbose = args.verbose,
          sessions = List(args.session))

      val sessions_order =
        base_info.sessions_structure.imports_topological_order.zipWithIndex.
          toMap.withDefaultValue(-1)

      val results_json =
        JSON.Object(
          "return_code" -> results.rc,
          "sessions" ->
            results.sessions.toList.sortBy(sessions_order).map(session =>
              JSON.Object(
                "session" -> session,
                "return_code" -> results(session).rc,
                "timeout" -> results(session).timeout,
                "timing" -> results(session).timing.json)))

      if (results.ok) (results_json, results, base_info)
      else throw new Server.Error("Session build failed: return code " + results.rc, results_json)
    }
  }

  object Session_Start
  {
    sealed case class Args(
      build: Session_Build.Args,
      print_mode: List[String] = Nil)

    def unapply(json: JSON.T): Option[Args] =
      for {
        build <- Session_Build.unapply(json)
        print_mode <- JSON.list_default(json, "print_mode", JSON.Value.String.unapply _)
      }
      yield Args(build = build, print_mode = print_mode)

    def command(progress: Progress, args: Args, log: Logger = No_Logger)
      : (JSON.Object.T, (String, Thy_Resources.Session)) =
    {
      val base_info = Session_Build.command(progress, args.build)._3

      val session =
        Thy_Resources.start_session(
          base_info.options,
          base_info.session,
          session_dirs = base_info.dirs,
          session_base = Some(base_info.check_base),
          print_mode = args.print_mode,
          progress = progress,
          log = log)

      val id = Library.UUID()
      val res = JSON.Object("session_name" -> base_info.session, "session_id" -> id)

      (res, id -> session)
    }
  }

  object Session_Stop
  {
    def unapply(json: JSON.T): Option[String] =
      JSON.string(json, "session_id")

    def command(session: Thy_Resources.Session): (JSON.Object.T, Process_Result) =
    {
      val result = session.stop()
      val result_json = JSON.Object("return_code" -> result.rc)

      if (result.ok) (result_json, result)
      else throw new Server.Error("Session shutdown failed: return code " + result.rc, result_json)
    }
  }

  object Use_Theories
  {
    sealed case class Args(
      session_id: String,
      theories: List[(String, Position.T)],
      qualifier: String = default_qualifier,
      master_dir: String = "")

    def unapply(json: JSON.T): Option[Args] =
      for {
        session_id <- JSON.string(json, "session_id")
        theories <- JSON.list(json, "theories", unapply_name_pos _)
        qualifier <- JSON.string_default(json, "qualifier", default_qualifier)
        master_dir <- JSON.string_default(json, "master_dir")
      }
      yield Args(session_id, theories, qualifier = qualifier, master_dir = master_dir)

    def command(args: Args,
      session: Thy_Resources.Session,
      id: String = Library.UUID(),
      progress: Progress = No_Progress): (JSON.Object.T, Thy_Resources.Theories_Result) =
    {
      val result =
        session.use_theories(args.theories, qualifier = args.qualifier,
          master_dir = args.master_dir, id = id, progress = progress)

      val result_json =
        JSON.Object(
          "ok" -> result.ok,
          "nodes" ->
            (for ((name, st) <- result.nodes) yield
              JSON.Object("node_name" -> name.node, "theory" -> name.theory, "status" -> st.json)))

      (result_json, result)
    }
  }
}
