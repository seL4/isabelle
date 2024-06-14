/*  Title:      Tools/VSCode/src/dynamic_output.scala
    Author:     Makarius

Dynamic output, depending on caret focus: messages, state etc.
*/

package isabelle.vscode


import isabelle._


object Dynamic_Output {
  def apply(server: Language_Server): Dynamic_Output = new Dynamic_Output(server)
}

class Dynamic_Output private(server: Language_Server) {
  private val pretty_panel_ = Synchronized(None: Option[Pretty_Text_Panel])
  def pretty_panel: Pretty_Text_Panel = pretty_panel_.value.getOrElse(error("No Pretty Panel for Dynamic Output"))

  private def handle_update(restriction: Option[Set[Command]], force: Boolean = false): Unit = {
    val output =
      server.resources.get_caret() match {
        case None => Some(Nil)
        case Some(caret) =>
          val snapshot = server.resources.snapshot(caret.model)
          snapshot.current_command(caret.node_name, caret.offset) match {
            case None => Some(Nil)
            case Some(command) =>
              if (restriction.isEmpty || restriction.get.contains(command)) {
                val output_state = server.resources.options.bool("editor_output_state")
                Some(Rendering.output_messages(snapshot.command_results(command), output_state))
              } else None
          }
      }
      
    output match {
      case None =>
      case Some(output) => pretty_panel.refresh(output)
    }
  }


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case changed: Session.Commands_Changed =>
        handle_update(if (changed.assignment) None else Some(changed.commands))

      case Session.Caret_Focus =>
        handle_update(None)
    }

  def init(): Unit = {
    server.session.commands_changed += main
    server.session.caret_focus += main
    pretty_panel_.change(p => Some(Pretty_Text_Panel(
      server.resources,
      server.channel,
      (output_text, decorations) => { server.channel.write(LSP.Dynamic_Output(output_text, decorations)) }
    )))
    handle_update(None)
  }

  def exit(): Unit = {
    server.session.commands_changed -= main
    server.session.caret_focus -= main
  }

  def set_margin(margin: Double): Unit = {
    pretty_panel.update_margin(margin)
  }
}
