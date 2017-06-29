/*  Title:      Tools/VSCode/src/build_html.scala
    Author:     Makarius

JavaScript snippets for VSCode HTML view.
*/

package isabelle.vscode


import isabelle._


object VSCode_JavaScript
{
  val invoke_command =
"""
function invoke_command(name, args)
{
  window.parent.postMessage(
    {
      command: "did-click-link",
      data: "command:" + encodeURIComponent(name) + "?" + encodeURIComponent(JSON.stringify(args))
    }, "file://")
}
"""
}
