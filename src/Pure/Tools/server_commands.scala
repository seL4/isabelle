/*  Title:      Pure/Tools/server_commands.scala
    Author:     Makarius

Miscellaneous Isabelle server commands.
*/

package isabelle


object Server_Commands
{
  def default_preferences: String = Options.read_prefs()

  object Help extends Server.Command("help")
  {
    override val command_body: Server.Command_Body =
      { case (context, ()) => context.command_list }
  }

  object Echo extends Server.Command("echo")
  {
    override val command_body: Server.Command_Body =
      { case (_, t) => t }
  }

  object Cancel extends Server.Command("cancel")
  {
    sealed case class Args(task: UUID.T)

    def unapply(json: JSON.T): Option[Args] =
      for { task <- JSON.uuid(json, "task") }
      yield Args(task)

    override val command_body: Server.Command_Body =
      { case (context, Cancel(args)) => context.cancel_task(args.task) }
  }

  object Shutdown extends Server.Command("shutdown")
  {
    override val command_body: Server.Command_Body =
      { case (context, ()) => context.server.shutdown() }
  }

  object Session_Build extends Server.Command("session_build")
  {
    sealed case class Args(
      session: String,
      preferences: String = default_preferences,
      options: List[String] = Nil,
      dirs: List[String] = Nil,
      include_sessions: List[String] = Nil,
      verbose: Boolean = false)

    def unapply(json: JSON.T): Option[Args] =
      for {
        session <- JSON.string(json, "session")
        preferences <- JSON.string_default(json, "preferences", default_preferences)
        options <- JSON.strings_default(json, "options")
        dirs <- JSON.strings_default(json, "dirs")
        include_sessions <- JSON.strings_default(json, "include_sessions")
        verbose <- JSON.bool_default(json, "verbose")
      }
      yield {
        Args(session, preferences = preferences, options = options, dirs = dirs,
          include_sessions = include_sessions, verbose = verbose)
      }

    def command(args: Args, progress: Progress = new Progress)
      : (JSON.Object.T, Build.Results, Options, Sessions.Base_Info) =
    {
      val options = Options.init(prefs = args.preferences, opts = args.options)
      val dirs = args.dirs.map(Path.explode)

      val base_info =
        Sessions.base_info(options, args.session, progress = progress, dirs = dirs,
          include_sessions = args.include_sessions).check

      val results =
        Build.build(options,
          selection = Sessions.Selection.session(args.session),
          progress = progress,
          build_heap = true,
          dirs = dirs,
          infos = base_info.infos,
          verbose = args.verbose)

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

      if (results.ok) (results_json, results, options, base_info)
      else {
        throw new Server.Error("Session build failed: " + Process_Result.print_rc(results.rc),
          results_json)
      }
    }

    override val command_body: Server.Command_Body =
      { case (context, Session_Build(args)) =>
        context.make_task(task => Session_Build.command(args, progress = task.progress)._1) }
  }

  object Session_Start extends Server.Command("session_start")
  {
    sealed case class Args(
      build: Session_Build.Args,
      print_mode: List[String] = Nil)

    def unapply(json: JSON.T): Option[Args] =
      for {
        build <- Session_Build.unapply(json)
        print_mode <- JSON.strings_default(json, "print_mode")
      }
      yield Args(build = build, print_mode = print_mode)

    def command(args: Args, progress: Progress = new Progress, log: Logger = No_Logger)
      : (JSON.Object.T, (UUID.T, Headless.Session)) =
    {
      val (_, _, options, base_info) =
        try { Session_Build.command(args.build, progress = progress) }
        catch { case exn: Server.Error => error(exn.message) }

      val resources = Headless.Resources(options, base_info, log = log)

      val session = resources.start_session(print_mode = args.print_mode, progress = progress)

      val id = UUID.random()

      val res =
        JSON.Object(
          "session_id" -> id.toString,
          "tmp_dir" -> File.path(session.tmp_dir).implode)

      (res, id -> session)
    }

    override val command_body: Server.Command_Body =
      { case (context, Session_Start(args)) =>
          context.make_task(task =>
          {
            val (res, entry) =
              Session_Start.command(args, progress = task.progress, log = context.server.log)
            context.server.add_session(entry)
            res
          })
      }
  }

  object Session_Stop extends Server.Command("session_stop")
  {
    def unapply(json: JSON.T): Option[UUID.T] =
      JSON.uuid(json, "session_id")

    def command(session: Headless.Session): (JSON.Object.T, Process_Result) =
    {
      val result = session.stop()
      val result_json = JSON.Object("ok" -> result.ok, "return_code" -> result.rc)

      if (result.ok) (result_json, result)
      else throw new Server.Error("Session shutdown failed: " + result.print_rc, result_json)
    }

    override val command_body: Server.Command_Body =
      { case (context, Session_Stop(id)) =>
        context.make_task(_ =>
        {
          val session = context.server.remove_session(id)
          Session_Stop.command(session)._1
        })
      }
  }

  object Use_Theories extends Server.Command("use_theories")
  {
    sealed case class Args(
      session_id: UUID.T,
      theories: List[String],
      master_dir: String = "",
      pretty_margin: Double = Pretty.default_margin,
      unicode_symbols: Boolean = false,
      export_pattern: String = "",
      check_delay: Option[Time] = None,
      check_limit: Option[Int] = None,
      watchdog_timeout: Option[Time] = None,
      nodes_status_delay: Option[Time] = None,
      commit_cleanup_delay: Option[Time] = None)

    def unapply(json: JSON.T): Option[Args] =
      for {
        session_id <- JSON.uuid(json, "session_id")
        theories <- JSON.strings(json, "theories")
        master_dir <- JSON.string_default(json, "master_dir")
        pretty_margin <- JSON.double_default(json, "pretty_margin", Pretty.default_margin)
        unicode_symbols <- JSON.bool_default(json, "unicode_symbols")
        export_pattern <- JSON.string_default(json, "export_pattern")
        check_delay = JSON.seconds(json, "check_delay")
        check_limit = JSON.int(json, "check_limit")
        watchdog_timeout = JSON.seconds(json, "watchdog_timeout")
        nodes_status_delay = JSON.seconds(json, "nodes_status_delay")
        commit_cleanup_delay = JSON.seconds(json, "commit_cleanup_delay")
      }
      yield {
        Args(session_id, theories, master_dir = master_dir, pretty_margin = pretty_margin,
          unicode_symbols = unicode_symbols, export_pattern = export_pattern,
          check_delay = check_delay, check_limit = check_limit, watchdog_timeout = watchdog_timeout,
          nodes_status_delay = nodes_status_delay, commit_cleanup_delay = commit_cleanup_delay)
      }

    def command(args: Args,
      session: Headless.Session,
      id: UUID.T = UUID.random(),
      progress: Progress = new Progress): (JSON.Object.T, Headless.Use_Theories_Result) =
    {
      val result =
        session.use_theories(args.theories, master_dir = args.master_dir,
          check_delay = args.check_delay.getOrElse(session.default_check_delay),
          check_limit = args.check_limit.getOrElse(session.default_check_limit),
          watchdog_timeout = args.watchdog_timeout.getOrElse(session.default_watchdog_timeout),
          nodes_status_delay = args.nodes_status_delay.getOrElse(session.default_nodes_status_delay),
          commit_cleanup_delay =
            args.commit_cleanup_delay.getOrElse(session.default_commit_cleanup_delay),
          id = id, progress = progress)

      def output_text(s: String): String =
        if (args.unicode_symbols) Symbol.decode(s) else Symbol.encode(s)

      def output_message(tree: XML.Tree, pos: Position.T): JSON.Object.T =
      {
        val position = "pos" -> Position.JSON(pos)
        tree match {
          case XML.Text(msg) => Server.Reply.message(output_text(msg)) + position
          case elem: XML.Elem =>
            val msg = XML.content(Pretty.formatted(List(elem), margin = args.pretty_margin))
            val kind =
              Markup.messages.collectFirst({ case (a, b) if b == elem.name =>
                if (Protocol.is_legacy(elem)) Markup.WARNING else a }) getOrElse ""
            Server.Reply.message(output_text(msg), kind = kind) + position
        }
      }

      val result_json =
        JSON.Object(
          "ok" -> result.ok,
          "errors" ->
            (for {
              (name, status) <- result.nodes if !status.ok
              (tree, pos) <- result.snapshot(name).messages if Protocol.is_error(tree)
            } yield output_message(tree, pos)),
          "nodes" ->
            (for ((name, status) <- result.nodes) yield {
              val snapshot = result.snapshot(name)
              name.json +
                ("status" -> status.json) +
                ("messages" ->
                  (for {
                    (tree, pos) <- snapshot.messages if Protocol.is_exported(tree)
                  } yield output_message(tree, pos))) +
                ("exports" ->
                  (if (args.export_pattern == "") Nil else {
                    val matcher = Export.make_matcher(args.export_pattern)
                    for { entry <- snapshot.exports if matcher(entry.theory_name, entry.name) }
                    yield {
                      val (base64, body) = entry.uncompressed.maybe_base64
                      JSON.Object("name" -> entry.name, "base64" -> base64, "body" -> body)
                    }
                  }))
            }))

      (result_json, result)
    }

    override val command_body: Server.Command_Body =
      { case (context, Use_Theories(args)) =>
        context.make_task(task =>
        {
          val session = context.server.the_session(args.session_id)
          Use_Theories.command(args, session, id = task.id, progress = task.progress)._1
        })
      }
  }

  object Purge_Theories extends Server.Command("purge_theories")
  {
    sealed case class Args(
      session_id: UUID.T,
      theories: List[String] = Nil,
      master_dir: String = "",
      all: Boolean = false)

    def unapply(json: JSON.T): Option[Args] =
      for {
        session_id <- JSON.uuid(json, "session_id")
        theories <- JSON.strings_default(json, "theories")
        master_dir <- JSON.string_default(json, "master_dir")
        all <- JSON.bool_default(json, "all")
      }
      yield { Args(session_id, theories = theories, master_dir = master_dir, all = all) }

    def command(args: Args, session: Headless.Session)
      : (JSON.Object.T, (List[Document.Node.Name], List[Document.Node.Name])) =
    {
      val (purged, retained) =
        session.purge_theories(
          theories = args.theories, master_dir = args.master_dir, all = args.all)

      val result_json =
        JSON.Object("purged" -> purged.map(_.json), "retained" -> retained.map(_.json))

      (result_json, (purged, retained))
    }

    override val command_body: Server.Command_Body =
      { case (context, Purge_Theories(args)) =>
        val session = context.server.the_session(args.session_id)
        command(args, session)._1
      }
  }
}

class Server_Commands extends Server.Commands(
  Server_Commands.Help,
  Server_Commands.Echo,
  Server_Commands.Cancel,
  Server_Commands.Shutdown,
  Server_Commands.Session_Build,
  Server_Commands.Session_Start,
  Server_Commands.Session_Stop,
  Server_Commands.Use_Theories,
  Server_Commands.Purge_Theories)
