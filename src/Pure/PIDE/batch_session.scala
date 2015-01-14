/*  Title:      Pure/Tools/batch_session.scala
    Author:     Makarius

PIDE session in batch mode.
*/

package isabelle


import isabelle._


object Batch_Session
{
  def batch_session(
    options: Options,
    verbose: Boolean = false,
    dirs: List[Path] = Nil,
    session: String): Boolean =
  {
    val (_, session_tree) =
      Build.find_sessions(options, dirs).selection(false, false, Nil, List(session))
    val session_info = session_tree(session)
    val parent_session =
      session_info.parent getOrElse error("No parent session for " + quote(session))

    if (Build.build(options, new Build.Console_Progress(verbose),
        verbose = verbose, build_heap = true,
        dirs = dirs, sessions = List(parent_session)) != 0)
      new RuntimeException

    val deps = Build.dependencies(Build.Ignore_Progress, false, verbose, false, session_tree)
    val resources =
    {
      val content = deps(parent_session)
      new Resources(content.loaded_theories, content.known_theories, content.syntax)
    }

    val progress = new Build.Console_Progress(verbose)

    val session_result = Future.promise[Unit]
    @volatile var build_theories_result: Option[Promise[Boolean]] = None

    val prover_session = new Session(resources)

    prover_session.phase_changed +=
      Session.Consumer[Session.Phase](getClass.getName) {
        case Session.Ready =>
          prover_session.add_protocol_handler(Build.handler_name)
          val master_dir = session_info.dir
          val theories = session_info.theories.map({ case (_, opts, thys) => (opts, thys) })
          build_theories_result =
            Some(Build.build_theories(prover_session, master_dir, theories))
        case Session.Inactive | Session.Failed =>
          session_result.fulfill_result(Exn.Exn(ERROR("Prover process terminated")))
        case Session.Shutdown =>
          session_result.fulfill(())
        case _ =>
      }

    prover_session.all_messages +=
      Session.Consumer[Prover.Message](getClass.getName) {
        case msg: Prover.Output =>
          msg.properties match {
            case Markup.Loading_Theory(name) => progress.theory(session, name)
            case _ =>
          }
        case _ =>
      }

    prover_session.start("Isabelle", List("-r", "-q", parent_session))

    session_result.join
    build_theories_result match {
      case None => false
      case Some(promise) => promise.join
    }
  }
}

