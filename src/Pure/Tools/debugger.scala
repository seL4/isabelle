/*  Title:      Pure/Tools/debugger.scala
    Author:     Makarius

Interactive debugger for Isabelle/ML.
*/

package isabelle


object Debugger
{
  /* global state */

  case class State(
    output: Map[String, Command.Results] = Map.empty)  // thread name ~> output messages
  {
    def add_output(name: String, entry: Command.Results.Entry): State =
      copy(output = output + (name -> (output.getOrElse(name, Command.Results.empty) + entry)))
  }

  private val global_state = Synchronized(State())
  def current_state(): State = global_state.value


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
        case Markup.Debugger_Output(name) =>
          val msg_body =
            prover.xml_cache.body(
              YXML.parse_body_failsafe(UTF8.decode_permissive(msg.bytes)))
          msg_body match {
            case List(XML.Elem(Markup(name, props @ Markup.Serial(i)), body)) =>
              val message = XML.Elem(Markup(Markup.message(name), props), body)
              global_state.change(_.add_output(name, i -> message))
              true
            case _ => false
          }
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
