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

  def init(server: Language_Server)
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

  def auto_update(id: Counter.ID, enabled: Boolean): Unit =
    instances.value.get(id).foreach(state =>
      state.server.editor.send_dispatcher(state.auto_update(Some(enabled))))
}


class State_Panel private(val server: Language_Server)
{
  /* output */

  val id: Counter.ID = State_Panel.make_id()

  private def output(content: String): Unit =
    server.channel.write(LSP.State_Output(id, content))


  /* query operation */

  private val output_active = Synchronized(true)

  private val print_state =
    new Query_Operation(server.editor, (), "print_state", _ => (),
      (snapshot, results, body) =>
        if (output_active.value) {
          val text = server.resources.output_pretty_message(Pretty.separate(body))
          val content =
            HTML.output_document(
              List(HTML.style(HTML.fonts_css()),
                HTML.style_file(HTML.isabelle_css),
                HTML.script(controls_script)),
              List(controls, HTML.source(text)),
              css = "", structural = true)
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

  def auto_update(set: Option[Boolean] = None)
  {
    val enabled =
      auto_update_enabled.guarded_access(a =>
        set match {
          case None => Some((a, a))
          case Some(b) => Some((b, b))
        })
    if (enabled) update()
  }


  /* controls */

  private def controls_script =
"""
const vscode = acquireVsCodeApi();

function invoke_auto_update(enabled)
{ vscode.postMessage({'command': 'auto_update', 'enabled': enabled}) }

function invoke_update()
{ vscode.postMessage({'command': 'update'}) }

function invoke_locate()
{ vscode.postMessage({'command': 'locate'}) }
"""

  private def auto_update_button: XML.Elem =
    HTML.GUI.checkbox(HTML.text("Auto update"),
      name = "auto_update",
      tooltip = "Indicate automatic update following cursor movement",
      selected = auto_update_enabled.value,
      script = "invoke_auto_update(this.checked)")

  private def update_button: XML.Elem =
    HTML.GUI.button(List(HTML.bold(HTML.text("Update"))),
      name = "update",
      tooltip = "Update display according to the command at cursor position",
      script = "invoke_update()")

  private def locate_button: XML.Elem =
    HTML.GUI.button(HTML.text("Locate"),
      name = "locate",
      tooltip = "Locate printed command within source text",
      script = "invoke_locate()")

  private def controls: XML.Elem =
    HTML.Wrap_Panel(List(auto_update_button, update_button, locate_button))


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
    output_active.change(_ => false)
    server.session.commands_changed -= main
    server.session.caret_focus -= main
    server.editor.send_wait_dispatcher { print_state.deactivate() }
  }
}
