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
    def empty(session: String, timeout: Time): Session_Context =
      new Session_Context(session, timeout, Time.zero, Nil)

    def apply(
      session: String,
      timeout: Time,
      store: Sessions.Store,
      progress: Progress = new Progress
    ): Session_Context = {
      store.try_open_database(session) match {
        case None => empty(session, timeout)
        case Some(db) =>
          def ignore_error(msg: String) = {
            progress.echo_warning("Ignoring bad database " + db +
              " for session " + quote(session) + (if (msg == "") "" else ":\n" + msg))
            empty(session, timeout)
          }
          try {
            val command_timings = store.read_command_timings(db, session)
            val elapsed =
              store.read_session_timing(db, session) match {
                case Markup.Elapsed(s) => Time.seconds(s)
                case _ => Time.zero
              }
            new Session_Context(session, timeout, elapsed, command_timings)
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
    val timeout: Time,
    val old_time: Time,
    val old_command_timings: List[Properties.T]
  ) {
    def is_empty: Boolean = old_time.is_zero && old_command_timings.isEmpty

    override def toString: String = session
  }

  object Context {
    def apply(
      sessions_structure: Sessions.Structure,
      store: Sessions.Store,
      progress: Progress = new Progress
    ): Context = {
      val build_graph = sessions_structure.build_graph

      val sessions =
        Map.from(
          for (name <- build_graph.keys_iterator)
          yield {
            val timeout = sessions_structure(name).timeout
            name -> Build_Process.Session_Context(name, timeout, store, progress = progress)
          })

      val sessions_time = {
        val maximals = build_graph.maximals.toSet
        def descendants_time(name: String): Double = {
          if (maximals.contains(name)) sessions(name).old_time.seconds
          else {
            val descendants = build_graph.all_succs(List(name)).toSet
            val g = build_graph.restrict(descendants)
            (0.0 :: g.maximals.flatMap { desc =>
              val ps = g.all_preds(List(desc))
              if (ps.exists(p => !sessions.isDefinedAt(p))) None
              else Some(ps.map(p => sessions(p).old_time.seconds).sum)
            }).max
          }
        }
        Map.from(
          for (name <- sessions.keysIterator)
          yield name -> descendants_time(name)).withDefaultValue(0.0)
      }

      val ordering =
        new Ordering[String] {
          def compare(name1: String, name2: String): Int =
            sessions_time(name2) compare sessions_time(name1) match {
              case 0 =>
                sessions(name2).timeout compare sessions(name1).timeout match {
                  case 0 => name1 compare name2
                  case ord => ord
                }
              case ord => ord
            }
        }

      new Context(sessions_structure, sessions, ordering)
    }
  }

  final class Context private(
    val sessions_structure: Sessions.Structure,
    sessions: Map[String, Session_Context],
    val ordering: Ordering[String]
  ) {
    def apply(session: String): Session_Context =
      sessions.getOrElse(session, Session_Context.empty(session, Time.zero))

    def build_heap(session: String): Boolean =
      Sessions.is_pure(session) || !sessions_structure.build_graph.is_maximal(session)
  }
}
