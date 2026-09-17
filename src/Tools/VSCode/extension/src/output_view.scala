/*  Title:      Tools/VSCode/extension/output_view.scala
    Author:     Fabian Huch

Output view within Isabelle/VSCode extension.
*/

package isabelle.vscode.extension

import org.scalajs.dom

import isabelle._


object Output_View {
  private val vscode = Webview_Api.acquire

  val pretty_text_area =
    new Pretty_Text_Area(output => Scalajs.DOM.update(HTML.control_markup(output, hidden = true)))


  /* main */

  def main(): Unit = {
    dom.window.onresize = { _ => pretty_text_area.on_resize() }
    dom.window.onload = { _ => pretty_text_area.on_load() }

    Webview_Api.on_message { e =>
      pretty_text_area.handle_update(YXML.parse_body(YXML.Source(e.data.toString)))
    }

    vscode.post(JSON.Object("command" -> "ready"))
  }
}
