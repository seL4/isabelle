/*  Title:      Pure/System/isabelle_process.scala
    Author:     Makarius

Isabelle process wrapper.
*/

package isabelle


import java.io.{File => JFile}


object Isabelle_Process
{
  def start(
    session: Session,
    options: Options,
    sessions_structure: Sessions.Structure,
    store: Sessions.Store,
    logic: String = "",
    raw_ml_system: Boolean = false,
    use_prelude: List[String] = Nil,
    eval_main: String = "",
    modes: List[String] = Nil,
    cwd: JFile = null,
    env: Map[String, String] = Isabelle_System.settings()): Isabelle_Process =
  {
    val channel = System_Channel()
    val process =
      try {
        val channel_options =
          options.string.update("system_channel_address", channel.address).
            string.update("system_channel_password", channel.password)
        ML_Process(channel_options, sessions_structure, store,
          logic = logic, raw_ml_system = raw_ml_system,
          use_prelude = use_prelude, eval_main = eval_main,
          modes = modes, cwd = cwd, env = env)
      }
      catch { case exn @ ERROR(_) => channel.shutdown(); throw exn }
    process.stdin.close()

    val isabelle_process = new Isabelle_Process(session, process)
    session.start(receiver => new Prover(receiver, session.cache, channel, process))

    isabelle_process
  }
}

class Isabelle_Process private(session: Session, process: Bash.Process)
{
  private val startup = Future.promise[String]
  private val terminated = Future.promise[Process_Result]

  session.phase_changed +=
    Session.Consumer(getClass.getName) {
      case Session.Ready =>
        startup.fulfill("")
      case Session.Terminated(result) =>
        if (!result.ok && !startup.is_finished) {
          val syslog = session.syslog_content()
          val err = "Session startup failed" + (if (syslog.isEmpty) "" else ":\n" + syslog)
          startup.fulfill(err)
        }
        terminated.fulfill(result)
      case _ =>
    }

  def await_startup(): Isabelle_Process =
    startup.join match {
      case "" => this
      case err => session.stop(); error(err)
    }

  def await_shutdown(): Process_Result =
  {
    val result = terminated.join
    session.stop()
    result
  }

  def terminate(): Unit = process.terminate()
}
