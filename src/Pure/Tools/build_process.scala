/*  Title:      Pure/Tools/build_process.scala
    Author:     Makarius

Build process for sessions, with build database, optional heap, and
optional presentation.
*/

package isabelle


import scala.math.Ordering


object Build_Process {
  /* static information */

  object Session_Context {
    def empty(session: String): Session_Context = new Session_Context(session, Time.zero, Nil)

    def apply(
      session: String,
      store: Sessions.Store,
      progress: Progress = new Progress
    ): Session_Context = {
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
            new Session_Context(session, elapsed, command_timings)
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

  final class Session_Context(
    val session: String,
    val old_time: Time,
    val old_command_timings: List[Properties.T]
  ) {
    def is_empty: Boolean = old_time.is_zero && old_command_timings.isEmpty

    override def toString: String = session
  }

  object Context {
    private def make_session_timing(
      sessions_structure: Sessions.Structure,
      timing: Map[String, Double]
    ) : Map[String, Double] = {
      val maximals = sessions_structure.build_graph.maximals.toSet
      def desc_timing(session_name: String): Double = {
        if (maximals.contains(session_name)) timing(session_name)
        else {
          val descendants = sessions_structure.build_descendants(List(session_name)).toSet
          val g = sessions_structure.build_graph.restrict(descendants)
          (0.0 :: g.maximals.flatMap { desc =>
            val ps = g.all_preds(List(desc))
            if (ps.exists(p => !timing.isDefinedAt(p))) None
            else Some(ps.map(timing(_)).sum)
          }).max
        }
      }
      timing.keySet.iterator.map(name => (name -> desc_timing(name))).toMap.withDefaultValue(0.0)
    }

    def apply(
      sessions_structure: Sessions.Structure,
      store: Sessions.Store,
      progress: Progress = new Progress
    ): Context = {
      val sessions =
        Map.from(
          for (session <- sessions_structure.build_graph.keys_iterator)
          yield session -> Build_Process.Session_Context(session, store, progress = progress))

      val session_timing =
        make_session_timing(sessions_structure,
          Map.from(for ((name, context) <- sessions.iterator) yield name -> context.old_time.seconds))

      val ordering =
        new Ordering[String] {
          def compare(name1: String, name2: String): Int =
            session_timing(name2) compare session_timing(name1) match {
              case 0 =>
                sessions_structure(name2).timeout compare sessions_structure(name1).timeout match {
                  case 0 => name1 compare name2
                  case ord => ord
                }
              case ord => ord
            }
        }

      new Context(sessions, ordering)
    }
  }

  final class Context private(
    sessions: Map[String, Session_Context],
    val ordering: Ordering[String]
  ) {
    def apply(session: String): Session_Context =
      sessions.getOrElse(session, Session_Context.empty(session))
  }
}
