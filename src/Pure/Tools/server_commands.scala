/*  Title:      Pure/Tools/server_commands.scala
    Author:     Makarius

Miscellaneous Isabelle server commands.
*/

package isabelle


object Server_Commands
{
  object Session_Build
  {
    sealed case class Args(
      session: String,
      prefs: String = "",
      opts: List[String] = Nil,
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
        prefs <- JSON.string_default(json, "preferences")
        opts <- JSON.list_default(json, "options", JSON.Value.String.unapply _)
        dirs <- JSON.list_default(json, "dirs", JSON.Value.String.unapply _)
        ancestor_session <- JSON.string_default(json, "ancestor_session")
        all_known <- JSON.bool_default(json, "all_known")
        focus_session <- JSON.bool_default(json, "focus_session")
        required_session <- JSON.bool_default(json, "required_session")
        system_mode <- JSON.bool_default(json, "system_mode")
        verbose <- JSON.bool_default(json, "verbose")
      }
      yield {
        Args(session, prefs = prefs, opts = opts, dirs = dirs, ancestor_session = ancestor_session,
          all_known = all_known, focus_session = focus_session, required_session = required_session,
          system_mode = system_mode, verbose = verbose)
      }

    def command(progress: Progress, args: Args): (JSON.T, Sessions.Base_Info, Build.Results) =
    {
      val options = Options.init(prefs = args.prefs, opts = args.opts)
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

      (JSON.Object("rc" -> results.rc), base_info, results)
    }
  }
}
