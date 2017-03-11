/*  Title:      Tools/VSCode/src/dynamic_output.scala
    Author:     Makarius

Dynamic output, depending on caret focus: messages, state etc.
*/

package isabelle.vscode


import isabelle._


object Dynamic_Output
{
  case class State(
    do_update: Boolean = true,
    snapshot: Document.Snapshot = Document.Snapshot.init,
    command: Command = Command.empty,
    results: Command.Results = Command.Results.empty,
    output: List[XML.Tree] = Nil)

  def apply(server: Server): Dynamic_Output = new Dynamic_Output(server)
}


class Dynamic_Output private(server: Server)
{
  private val state = Synchronized(Dynamic_Output.State())

  private def handle_update(restriction: Option[Set[Command]])
  {
    state.change(st =>
      {
        val resources = server.resources
        def init_st = Dynamic_Output.State(st.do_update)
        val st1 =
          resources.caret_range() match {
            case None => init_st
            case Some((model, caret_range)) =>
              val snapshot = model.snapshot()
              if (st.do_update && !snapshot.is_outdated) {
                model.current_command(snapshot, caret_range.start) match {
                  case None => init_st
                  case Some(command) =>
                    val results = snapshot.state.command_results(snapshot.version, command)
                    val output =
                      if (!restriction.isDefined || restriction.get.contains(command))
                        Rendering.output_messages(results)
                      else st.output
                    st.copy(
                      snapshot = snapshot, command = command, results = results, output = output)
                }
              }
              else st
          }
        if (st1.output != st.output) {
          server.channel.write(Protocol.Dynamic_Output(
            resources.output_pretty_message(Pretty.separate(st1.output))))
        }
        st1
      })
  }


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case changed: Session.Commands_Changed =>
        handle_update(if (changed.assignment) None else Some(changed.commands))

      case Session.Caret_Focus =>
        handle_update(None)
    }

  def init()
  {
    server.session.commands_changed += main
    server.session.caret_focus += main
    handle_update(None)
  }

  def exit()
  {
    server.session.commands_changed -= main
    server.session.caret_focus -= main
  }
}
