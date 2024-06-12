/*  Title:      Tools/VSCode/src/dynamic_output.scala
    Author:     Makarius

Dynamic output, depending on caret focus: messages, state etc.
*/

package isabelle.vscode


import isabelle._


object Dynamic_Output {
  sealed case class State(do_update: Boolean = true, output: List[XML.Tree] = Nil) {
    def handle_update(
      resources: VSCode_Resources,
      channel: Channel,
      restriction: Option[Set[Command]],
      margin: Double,
      force: Boolean,
    ): State = {
      val st1 =
        resources.get_caret() match {
          case None => copy(output = Nil)
          case Some(caret) =>
            val snapshot = resources.snapshot(caret.model)
            if (do_update && !snapshot.is_outdated) {
              snapshot.current_command(caret.node_name, caret.offset) match {
                case None => copy(output = Nil)
                case Some(command) =>
                  copy(output =
                    if (restriction.isEmpty || restriction.get.contains(command)) {
                      val output_state = resources.options.bool("editor_output_state")
                      Rendering.output_messages(snapshot.command_results(command), output_state)
                    } else output)
              }
            }
            else this
        }
      if (st1.output != output || force) {
        val (output, decorations) = resources.output_pretty_panel(st1.output, margin)
        channel.write(LSP.Dynamic_Output(output, decorations))
      }
      st1
    }
  }

  def apply(server: Language_Server): Dynamic_Output = new Dynamic_Output(server)
}


class Dynamic_Output private(server: Language_Server) {
  private val state = Synchronized(Dynamic_Output.State())
  private val margin_ = Synchronized(None: Option[Double])
  def margin: Double = margin_.value.getOrElse(server.resources.message_margin)

  private val delay_margin = Delay.last(server.resources.output_delay, server.channel.Error_Logger) {
    handle_update(None, force = true)
  }

  private def handle_update(restriction: Option[Set[Command]], force: Boolean = false): Unit = {
    state.change(
      _.handle_update(server.resources, server.channel, restriction, margin, force))
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
    handle_update(None)
  }

  def exit(): Unit = {
    server.session.commands_changed -= main
    server.session.caret_focus -= main
  }

  def set_margin(margin: Double): Unit = {
    margin_.change(_ => Some(margin))
    delay_margin.invoke()
  }
}
