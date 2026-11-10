/*  Title:      Tools/VSCode/extension/src/webviews.scala
    Author:     Fabian Huch

Base functionality for web views.
*/

package isabelle.vscode.extension

import VSCode.{Uri, Webview}
import isabelle._


object Webviews {
  val vscode_css = Path.make(List("media", "vscode.css"))
  val codicons_css = Path.make(List("node_modules", "@vscode", "codicons", "dist", "codicon.css"))
  val isabelle_font = Path.make(List("fonts", "IsabelleDejaVuSansMono.ttf"))
  def element_css(name: String): Path = {
    Path.make(
      List("node_modules", "@vscode-elements", "elements-lite", "components", name, name + ".css"))
  }

  def get_html(
    webview: Webview,
    extension_path: String,
    title: String,
    script_name: String
  ): String = {
    def uri(path: Path): String = {
      webview.web_uri(Uri.file(Url.append_path(extension_path, File.platform_path(path)))).toString
    }
    val vscode_elements = List("action-button", "button", "checkbox", "label", "textfield")

    """
<!DOCTYPE html>
<html lang="en">
  <head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <link href="""" + uri(codicons_css) + """" rel="stylesheet" type="text/css">
""" + vscode_elements.map(name =>
        "<link href=\"" + uri(element_css(name)) + "\" rel=\"stylesheet\" type=\"text/css\">")
          .mkString("\n") + """
    <link href="""" + uri(vscode_css) + """" rel="stylesheet" type="text/css">
    <style>
        @font-face {
            font-family: "Isabelle DejaVu Sans Mono";
            src: url(""" + uri(isabelle_font) + """);
        }
        """ + _get_decorations() + """
    </style>
    <title>""" + title + """</title>
  </head>
  <body>
    <script type="module" src="""" + uri(Path.make(List("js", script_name))) + """"></script>
  </body>
</html>"""
  }

  def _get_decorations(): String = {
    val style = new StringBuilder
    for (key <- Decorations.text_colors) {
      style.append(
        "body.vscode-light ." + key + " { color: " + VSCode_Lib.get_color(key, true) + " }\n")
      style.append(
        "body.vscode-dark ." + key + " { color: " + VSCode_Lib.get_color(key, false) + " }\n")
      }
    style.toString
  }
}
