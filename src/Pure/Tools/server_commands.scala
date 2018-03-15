/*  Title:      Pure/Tools/server_commands.scala
    Author:     Makarius

Miscellaneous Isabelle server commands.
*/

package isabelle


object Server_Commands
{
  def default_preferences: String = Options.read_prefs()

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
}
