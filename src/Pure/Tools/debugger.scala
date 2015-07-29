/*  Title:      Pure/Tools/debugger.scala
    Author:     Makarius

Interactive debugger for Isabelle/ML.
*/

package isabelle


object Debugger
{
  /* GUI interaction */

  case object Event


  /* manager thread */

  private lazy val manager: Consumer_Thread[Any] =
    Consumer_Thread.fork[Any]("Debugger.manager", daemon = true)(
      consume = (arg: Any) =>
      {
        // FIXME
        true
      },
      finish = () =>
      {
        // FIXME
      }
    )


  /* protocol handler */

  class Handler extends Session.Protocol_Handler
  {
    private def debugger_output(prover: Prover, msg: Prover.Protocol_Output): Boolean =
    {
      msg.properties match {
        case Markup.Debugger_Output(name, serial) =>
          // FIXME
          Output.writeln("debugger_output " + name + " " + serial + "\n" + msg.text)
          true
        case _ => false
      }
    }

    override def stop(prover: Prover)
    {
      manager.shutdown()
    }

    val functions =
      Map(Markup.DEBUGGER_OUTPUT -> debugger_output _)
  }


  /* protocol commands */

  def init(session: Session): Unit =
    session.protocol_command("Debugger.init")

  def cancel(session: Session, name: String): Unit =
    session.protocol_command("Debugger.cancel", name)

  def input(session: Session, name: String, msg: String*): Unit =
    session.protocol_command("Debugger.input", (name :: msg.toList):_*)
}
