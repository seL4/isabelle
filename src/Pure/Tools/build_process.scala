/*  Title:      Pure/Tools/build_process.scala
    Author:     Makarius

Build process for sessions, with build database, optional heap, and
optional presentation.
*/

package isabelle


object Build_Process {
  /* timings from session database */

  object Session_Timing {
    def empty(session: String): Session_Timing = new Session_Timing(session, Time.zero, Nil)

    def load(
      session: String,
      store: Sessions.Store,
      progress: Progress = new Progress
    ): Session_Timing = {
      store.try_open_database(session) match {
        case None => empty(session)
        case Some(db) =>
          def ignore_error(msg: String) = {
            progress.echo_warning("Ignoring bad database " + db +
              " for session " + quote(session) + (if (msg == "") "" else ":\n" + msg))
            empty(session)
          }
          try {
            val command_timings = store.read_command_timings(db, session)
            val elapsed =
              store.read_session_timing(db, session) match {
                case Markup.Elapsed(s) => Time.seconds(s)
                case _ => Time.zero
              }
            new Session_Timing(session, elapsed, command_timings)
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

  final class Session_Timing(
    val session: String,
    val elapsed: Time,
    val command_timings: List[Properties.T]
  ) {
    def is_empty: Boolean = elapsed.is_zero && command_timings.isEmpty

    override def toString: String =
      session + (if (elapsed.seconds > 0.0) " (" + elapsed.message_hms + " elapsed time)" else "")
  }
}
