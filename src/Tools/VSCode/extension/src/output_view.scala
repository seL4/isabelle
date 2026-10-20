/*  Title:      Tools/VSCode/extension/output_view.scala
    Author:     Fabian Huch

Output view within Isabelle/VSCode extension.
*/

package isabelle.vscode.extension

import org.scalajs.dom

import isabelle._


object Output_View {
  /* component */

  def main(): Unit = { new Output_View(Webview_Api.acquire).init() }
}

class Output_View private(vscode: Webview_Api) {
  val pretty_text_area =
    new Pretty_Text_Area(output => Scalajs.DOM.update(HTML.control_markup(output, hidden = true)))


  /* main */

  def init(): Unit = {
    Webview_Api.on_message { e =>
      pretty_text_area.handle_update(YXML.parse_body(YXML.Source(e.data.toString)))
    }

    pretty_text_area.init()
    vscode.post(JSON.Object("command" -> "ready"))
  }
}
