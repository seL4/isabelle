/*  Title:      Tools/VSCode/src/state_panel.scala
    Author:     Makarius

Show proof state.
*/

package isabelle.vscode


import isabelle._


object State_Panel
{
  private val make_id = Counter.make()
  private val instances = Synchronized(Map.empty[Counter.ID, State_Panel])

  def init(server: Server)
  {
    val instance = new State_Panel(server)
    instances.change(_ + (instance.id -> instance))
    instance.init()
  }

  def exit(id: Counter.ID)
  {
    instances.change(map =>
      map.get(id) match {
        case None => map
        case Some(instance) => instance.exit(); map - id
      })
  }

  def locate(id: Counter.ID): Unit =
    instances.value.get(id).foreach(state =>
      state.server.editor.send_dispatcher(state.locate()))

  def update(id: Counter.ID): Unit =
    instances.value.get(id).foreach(state =>
      state.server.editor.send_dispatcher(state.update()))
}


class State_Panel private(val server: Server)
{
  /* output */

  val id: Counter.ID = State_Panel.make_id()

  private def output(content: String): Unit =
    server.channel.write(Protocol.State_Output(id, content))


  /* query operation */

  private val print_state =
    new Query_Operation(server.editor, (), "print_state", _ => (),
      (snapshot, results, body) =>
        {
          val text = server.resources.output_pretty_message(Pretty.separate(body))
          val content =
            HTML.output_document(
              List(HTML.style(HTML.fonts_css()),
                HTML.style_file(Url.print_file(HTML.isabelle_css.file))),
              List(controls, HTML.source(text)),
              css = "")
          output(content)
        })

  def locate() { print_state.locate_query() }

  def update()
  {
    server.editor.current_node_snapshot(()) match {
      case Some(snapshot) =>
        (server.editor.current_command((), snapshot), print_state.get_location) match {
          case (Some(command1), Some(command2)) if command1.id == command2.id =>
          case _ => print_state.apply_query(Nil)
        }
      case None =>
    }
  }


  /* auto update */

  private val auto_update_enabled = Synchronized(true)

  def set_auto_update(b: Boolean) { auto_update_enabled.change(_ => b); if (b) update() }

  def auto_update() { if (auto_update_enabled.value) update() }


  /* controls */

  private def id_parameter: XML.Elem =
    HTML.GUI.parameter(id.toString, name = "id")

  private def auto_update_button: XML.Elem =
    HTML.GUI.checkbox(HTML.text("Auto update"),
      name = "auto_update",
      tooltip = "Indicate automatic update following cursor movement",
      submit = true,
      selected = auto_update_enabled.value)

  private def update_button: XML.Elem =
    HTML.GUI.button(List(HTML.bold(HTML.text("Update"))),
      name = "update",
      tooltip = "Update display according to the command at cursor position",
      submit = true)

  private def locate_button: XML.Elem =
    HTML.GUI.button(HTML.text("Locate"),
      name = "locate",
      tooltip = "Locate printed command within source text",
      submit = true)

  private val controls: XML.Elem =
    HTML.Wrap_Panel(
      contents = List(id_parameter, auto_update_button, update_button, locate_button),
      alignment = HTML.Wrap_Panel.Alignment.right)


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case changed: Session.Commands_Changed =>
        if (changed.assignment) auto_update()

      case Session.Caret_Focus =>
        auto_update()
    }

  def init()
  {
    server.session.commands_changed += main
    server.session.caret_focus += main
    server.editor.send_wait_dispatcher { print_state.activate() }
    server.editor.send_dispatcher { auto_update() }
  }

  def exit()
  {
    server.editor.send_wait_dispatcher { print_state.deactivate() }
    server.session.commands_changed -= main
    server.session.caret_focus -= main
  }
}
