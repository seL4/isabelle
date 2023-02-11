/*  Title:      Pure/Tools/build_process.scala
    Author:     Makarius

Build process for sessions, with build database, optional heap, and
optional presentation.
*/

package isabelle


object Build_Process {
  /* timings from session database */

  type Session_Timing = (List[Properties.T], Double)

  object Session_Timing {
    val empty: Session_Timing = (Nil, 0.0)

    def load(progress: Progress, store: Sessions.Store, session_name: String): Session_Timing = {
      store.try_open_database(session_name) match {
        case None => empty
        case Some(db) =>
          def ignore_error(msg: String) = {
            progress.echo_warning("Ignoring bad database " + db +
              " for session " + quote(session_name) + (if (msg == "") "" else ":\n" + msg))
            empty
          }
          try {
            val command_timings = store.read_command_timings(db, session_name)
            val session_timing =
              store.read_session_timing(db, session_name) match {
                case Markup.Elapsed(t) => t
                case _ => 0.0
              }
            (command_timings, session_timing)
          }
          catch {
            case ERROR(msg) => ignore_error(msg)
            case exn: java.lang.Error => ignore_error(Exn.message(exn))
            case _: XML.Error => ignore_error("XML.Error")
          }
          finally { db.close() }
      }
    }
  }
}
