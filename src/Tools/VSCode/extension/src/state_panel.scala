/*  Title:      Tools/VSCode/extension/state_panel.scala
    Author:     Fabian Huch

State panel within Isabelle/VSCode extension.
*/

package isabelle.vscode.extension

import org.scalajs.dom

import isabelle._


object State_Panel {
  private val vscode = Webview_Api.acquire


  /* gui state */

  private var auto_update_enabled = true


  /* controls */

  private def auto_update_button =
    HTML.GUI.checkbox(HTML.text("Auto update"),
      tooltip = "Indicate automatic update following cursor movement",
      selected = auto_update_enabled, script = auto_update_button_clicked.function("this.checked"))

  object auto_update_button_clicked extends Scalajs.Fun[Boolean] {
    def apply(state: Boolean): Unit = {
      auto_update_enabled = state
      vscode.post(JSON.Object("command" -> "auto_update", "enabled" -> auto_update_enabled))
    }
  }

  private val update_button =
    HTML.GUI.button(HTML.text("Update"),
      tooltip = "Update display according to the command at cursor position",
      script = update_button_clicked.function())

  object update_button_clicked extends Scalajs.Fun_Unit {
    def apply(): Unit = vscode.post(JSON.Object("command" -> "update"))
  }

  private val locate_button =
    HTML.GUI.button(HTML.text("Locate"),
      tooltip = "Update display according to the command at cursor position",
      script = locate_button_clicked.function())

  object locate_button_clicked extends Scalajs.Fun_Unit {
    def apply(): Unit = vscode.post(JSON.Object("command" -> "locate"))
  }

  private def controls = HTML.Wrap_Panel(List(auto_update_button, update_button, locate_button))


  /* main */

  def main(): Unit = {
    Pretty_Text_View.on_update { output =>
      Scalajs.DOM.update(HTML.control_markup(controls :: output, hidden = true))
    }

    dom.window.onresize = { _ => Pretty_Text_View.on_resize() }
    dom.window.onload = { _ => Pretty_Text_View.on_load() }

    Webview_Api.on_message { e =>
      val json = Scalajs.JSON.unapply(e.data).get

      for {
        content <- JSON.string(json, "content")
        auto_update <- JSON.bool(json, "auto_update")
      } {
        auto_update_enabled = auto_update
        Pretty_Text_View.handle_update(YXML.parse_body(YXML.Source(content)))
      }
    }

    vscode.post(JSON.Object("command" -> "ready"))
  }
}
