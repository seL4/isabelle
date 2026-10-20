/*  Title:      Tools/VSCode/extension/state_panel.scala
    Author:     Fabian Huch

State panel within Isabelle/VSCode extension.
*/

package isabelle.vscode.extension

import org.scalajs.dom

import isabelle._


object State_Panel {
  private val vscode = Webview_Api.acquire

  object auto_update_clicked extends Scalajs.Fun[Boolean] {
    def apply(state: Boolean): Unit = handle_auto_update(state)
  }
  object update_clicked extends Scalajs.Fun_Unit {
    def apply(): Unit = handle_update()
  }
  object locate_clicked extends Scalajs.Fun_Unit {
    def apply(): Unit = handle_locate()
  }

  /* gui state */

  private var auto_update_enabled = true


  /* controls */

  def handle_auto_update(state: Boolean): Unit = {
    auto_update_enabled = state
    vscode.post(JSON.Object("command" -> "auto_update", "enabled" -> auto_update_enabled))
  }
  private def auto_update_button =
    VSCode_Elements.checkbox("Auto update",
      tooltip = "Indicate automatic update following cursor movement",
      selected = auto_update_enabled, script = auto_update_clicked.function("this.checked"))

  def handle_update(): Unit = vscode.post(JSON.Object("command" -> "update"))
  private val update_button =
    VSCode_Elements.button("Update",
      tooltip = "Update display according to the command at cursor position",
      script = update_clicked.function())

  def handle_locate(): Unit = vscode.post(JSON.Object("command" -> "locate"))
  private val locate_button =
    VSCode_Elements.button("Locate", secondary = true,
      tooltip = "Update display according to the command at cursor position",
      script = locate_clicked.function())

  private def controls = HTML.Wrap_Panel(List(auto_update_button, update_button, locate_button))


  /* text area */

  private val pretty_text_area =
    new Pretty_Text_Area(output =>
      Scalajs.DOM.update(HTML.control_markup(controls :: output, hidden = true)))


  /* main */

  def main(): Unit = {
    Webview_Api.on_message { e =>
      val json = Scalajs.JSON.unapply(e.data).get

      for {
        content <- JSON.string(json, "content")
        auto_update <- JSON.bool(json, "auto_update")
      } {
        auto_update_enabled = auto_update
        pretty_text_area.handle_update(YXML.parse_body(YXML.Source(content)))
      }
    }

    vscode.post(JSON.Object("command" -> "ready"))
  }
}
