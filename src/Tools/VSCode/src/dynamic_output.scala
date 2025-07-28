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
  def pretty_panel: Pretty_Text_Panel =
    pretty_panel_.value.getOrElse(error("No Pretty Panel for Dynamic Output"))

  private def handle_update(restriction: Option[Set[Command]] = None): Unit = {
    val output =
      server.resources.get_caret() match {
        case None => Editor.Output.init
        case Some(caret) =>
          val snapshot = server.resources.snapshot(caret.model)
          server.editor.output(snapshot, caret.offset)
      }
    if (output.defined) pretty_panel.refresh(output.messages)
  }


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case changed: Session.Commands_Changed =>
        handle_update(restriction = if (changed.assignment) None else Some(changed.commands))

      case Session.Caret_Focus =>
        handle_update()
    }

  def init(): Unit = {
    server.session.commands_changed += main
    server.session.caret_focus += main
    pretty_panel_.change(_ =>
      Some(Pretty_Text_Panel(
        server.session,
        server.channel,
        LSP.Dynamic_Output.apply)))
    handle_update()
  }

  def exit(): Unit = {
    server.session.commands_changed -= main
    server.session.caret_focus -= main
  }

  def set_margin(margin: Double): Unit = {
    pretty_panel.update_margin(margin)
  }
}
