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

  object Cancel
  {
    sealed case class Args(task: UUID)

    def unapply(json: JSON.T): Option[Args] =
      for { task <- JSON.uuid(json, "task") }
      yield Args(task)
  }


  object Session_Build
  {
    sealed case class Args(
      session: String,
      preferences: String = default_preferences,
      options: List[String] = Nil,
      dirs: List[String] = Nil,
      all_known: Boolean = false,
      system_mode: Boolean = false,
      verbose: Boolean = false)

    def unapply(json: JSON.T): Option[Args] =
      for {
        session <- JSON.string(json, "session")
        preferences <- JSON.string_default(json, "preferences", default_preferences)
        options <- JSON.list_default(json, "options", JSON.Value.String.unapply _)
        dirs <- JSON.list_default(json, "dirs", JSON.Value.String.unapply _)
        all_known <- JSON.bool_default(json, "all_known")
        system_mode <- JSON.bool_default(json, "system_mode")
        verbose <- JSON.bool_default(json, "verbose")
      }
      yield {
        Args(session, preferences = preferences, options = options, dirs = dirs,
          all_known = all_known, system_mode = system_mode, verbose = verbose)
      }

    def command(args: Args, progress: Progress = No_Progress)
      : (JSON.Object.T, Build.Results, Sessions.Base_Info) =
    {
      val options = Options.init(prefs = args.preferences, opts = args.options)
      val dirs = args.dirs.map(Path.explode(_))

      val base_info =
        Sessions.base_info(options, args.session, progress = progress, dirs = dirs,
          all_known = args.all_known)
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
          "ok" -> results.ok,
          "return_code" -> results.rc,
          "sessions" ->
            results.sessions.toList.sortBy(sessions_order).map(session =>
              {
                val result = results(session)
                JSON.Object(
                  "session" -> session,
                  "ok" -> result.ok,
                  "return_code" -> result.rc,
                  "timeout" -> result.timeout,
                  "timing" -> result.timing.json)
              }))

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

    def command(args: Args, progress: Progress = No_Progress, log: Logger = No_Logger)
      : (JSON.Object.T, (UUID, Thy_Resources.Session)) =
    {
      val base_info =
        try { Session_Build.command(args.build, progress = progress)._3 }
        catch { case exn: Server.Error => error(exn.message) }

      val session =
        Thy_Resources.start_session(
          base_info.options,
          base_info.session,
          session_dirs = base_info.dirs,
          session_base = Some(base_info.check_base),
          print_mode = args.print_mode,
          progress = progress,
          log = log)

      val id = UUID()

      (JSON.Object("session_id" -> id.toString), id -> session)
    }
  }

  object Session_Stop
  {
    def unapply(json: JSON.T): Option[UUID] =
      JSON.uuid(json, "session_id")

    def command(session: Thy_Resources.Session): (JSON.Object.T, Process_Result) =
    {
      val result = session.stop()
      val result_json = JSON.Object("ok" -> result.ok, "return_code" -> result.rc)

      if (result.ok) (result_json, result)
      else throw new Server.Error("Session shutdown failed: return code " + result.rc, result_json)
    }
  }

  object Use_Theories
  {
    sealed case class Args(
      session_id: UUID,
      theories: List[(String, Position.T)],
      qualifier: String = default_qualifier,
      master_dir: String = "",
      pretty_margin: Double = Pretty.default_margin,
      unicode_symbols: Boolean = false)

    def unapply(json: JSON.T): Option[Args] =
      for {
        session_id <- JSON.uuid(json, "session_id")
        theories <- JSON.list(json, "theories", unapply_name_pos _)
        qualifier <- JSON.string_default(json, "qualifier", default_qualifier)
        master_dir <- JSON.string_default(json, "master_dir")
        pretty_margin <- JSON.double_default(json, "pretty_margin", Pretty.default_margin)
        unicode_symbols <- JSON.bool_default(json, "unicode_symbols")
      }
      yield {
        Args(session_id, theories, qualifier = qualifier, master_dir = master_dir,
          pretty_margin = pretty_margin, unicode_symbols)
      }

    def command(args: Args,
      session: Thy_Resources.Session,
      id: UUID = UUID(),
      progress: Progress = No_Progress): (JSON.Object.T, Thy_Resources.Theories_Result) =
    {
      val result =
        session.use_theories(args.theories, qualifier = args.qualifier,
          master_dir = args.master_dir, id = id, progress = progress)

      def output_text(s: String): String =
        if (args.unicode_symbols) Symbol.decode(s) else Symbol.encode(s)

      def output_message(tree: XML.Tree, pos: Position.T): JSON.Object.T =
      {
        val position = "pos" -> Position.JSON(pos)
        tree match {
          case XML.Text(msg) => Server.Reply.message(output_text(msg)) + position
          case elem: XML.Elem =>
            val msg = XML.content(Pretty.formatted(List(elem), margin = args.pretty_margin))
            val kind = Markup.messages.collectFirst({ case (a, b) if b == elem.name => a })
            Server.Reply.message(output_text(msg), kind = kind getOrElse "") + position
        }
      }

      val result_json =
        JSON.Object(
          "ok" -> result.ok,
          "errors" ->
            (for {
              (name, status) <- result.nodes if !status.ok
              (tree, pos) <- result.messages(name) if Protocol.is_error(tree)
            } yield output_message(tree, pos)),
          "nodes" ->
            (for ((name, status) <- result.nodes) yield
              JSON.Object(
                "node_name" -> name.node,
                "theory" -> name.theory,
                "status" -> status.json,
                "messages" ->
                  (for ((tree, pos) <- result.messages(name))
                    yield output_message(tree, pos)))))

      (result_json, result)
    }
  }
}
