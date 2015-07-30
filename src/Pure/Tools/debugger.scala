/*  Title:      Pure/Tools/debugger.scala
    Author:     Makarius

Interactive debugger for Isabelle/ML.
*/

package isabelle


object Debugger
{
  /* global state */

  sealed case class State(
    session: Session = new Session(Resources.empty),
    output: Map[String, Command.Results] = Map.empty)  // thread name ~> output messages
  {
    def add_output(name: String, entry: Command.Results.Entry): State =
      copy(output = output + (name -> (output.getOrElse(name, Command.Results.empty) + entry)))
  }

  private val global_state = Synchronized(State())
  def current_state(): State = global_state.value


  /* protocol handler */

  sealed case class Update(thread_names: Set[String])

  class Handler extends Session.Protocol_Handler
  {
    private var updated = Set.empty[String]
    private val delay_update =
      Simple_Thread.delay_first(current_state().session.output_delay) {
        current_state().session.debugger_updates.post(Update(updated))
        updated = Set.empty
      }
    private def update(name: String)
    {
      updated += name
      delay_update.invoke()
    }

    private def debugger_output(prover: Prover, msg: Prover.Protocol_Output): Boolean =
    {
      msg.properties match {
        case Markup.Debugger_Output(thread_name) =>
          val msg_body =
            prover.xml_cache.body(
              YXML.parse_body_failsafe(UTF8.decode_permissive(msg.bytes)))
          msg_body match {
            case List(XML.Elem(Markup(name, props @ Markup.Serial(i)), body)) =>
              val message = XML.Elem(Markup(Markup.message(name), props), body)
              global_state.change(_.add_output(thread_name, i -> message))
              update(thread_name)
              true
            case _ => false
          }
        case _ => false
      }
    }

    val functions =
      Map(Markup.DEBUGGER_OUTPUT -> debugger_output _)
  }


  /* protocol commands */

  def init(new_session: Session)
  {
    global_state.change(_.copy(session = new_session))
    current_state().session.protocol_command("Debugger.init")
  }

  def cancel(name: String): Unit =
    current_state().session.protocol_command("Debugger.cancel", name)

  def input(name: String, msg: String*): Unit =
    current_state().session.protocol_command("Debugger.input", (name :: msg.toList):_*)
}
