/*  Title:      Tools/VSCode/src/vscode_sledgehammer.scala
    Author:     Diana Korchmar, LMU Muenchen
    Author:     Makarius

Control panel for Sledgehammer.
*/

package isabelle.vscode


import isabelle._


class VSCode_Sledgehammer(server: Language_Server) {
  private val query_operation =
    new Query_Operation(server.editor, (), "sledgehammer", consume_status, consume_output)

  private def consume_status(status: Query_Operation.Status): Unit = {
    val message =
      status match {
        case Query_Operation.Status.waiting => "Waiting for evaluation of context ..."
        case Query_Operation.Status.running => "Sledgehammering ..."
        case Query_Operation.Status.finished => "Finished"
      }
    server.channel.write(LSP.Sledgehammer_Status(message))
  }

  private def consume_output(output: Editor.Output): Unit = {
    val content = YXML.string_of_body(Pretty.unbreakable(output.messages))
    server.channel.write(LSP.Sledgehammer_Output(content))
  }

  def provers(): Unit =
    server.channel.write(
      LSP.Sledgehammer_Provers_Response(server.options.string("sledgehammer_provers")))

  def request(args: List[String]): Unit =
    server.editor.send_dispatcher { query_operation.apply_query(args) }

  def cancel(): Unit = server.editor.send_dispatcher { query_operation.cancel_query() }
  def locate(): Unit = server.editor.send_dispatcher { query_operation.locate_query() }

  def init(): Unit = query_operation.activate()
  def exit(): Unit = query_operation.deactivate()
}
