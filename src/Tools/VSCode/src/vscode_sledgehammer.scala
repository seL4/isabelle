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

  def send_provers(): Unit = {
    val provers = server.options.string("sledgehammer_provers")
    server.channel.write(LSP.Sledgehammer_Provers_Response.apply(provers))
  }

  private def consume_status(status: Query_Operation.Status): Unit = {
    val msg =
      status match {
        case Query_Operation.Status.waiting => "Waiting for evaluation of context ..."
        case Query_Operation.Status.running => "Sledgehammering ..."
        case Query_Operation.Status.finished => "Finished"
      }
    server.channel.write(LSP.Sledgehammer_Status(msg))
  }

  private def consume_output(output: Editor.Output): Unit = {
    val content = XML.string_of_body(output.messages)
    server.channel.write(LSP.Sledgehammer_Output(content))
  }

  def request(args: List[String]): Unit =
    server.editor.send_dispatcher { query_operation.apply_query(args) }

  def sendback(text: String): Unit =
    server.editor.send_dispatcher {
      for {
        (snapshot, command) <- query_operation.query_command()
        node_pos <- snapshot.find_command_position(command.id, 0)
      } {
        val node_pos1 = node_pos.advance(command.source(command.core_range))
        server.channel.write(LSP.Sledgehammer_Insert(node_pos1, text))
      }
    }

  def cancel(): Unit = server.editor.send_dispatcher { query_operation.cancel_query() }
  def locate(): Unit = server.editor.send_dispatcher { query_operation.locate_query() }
  def init(): Unit = query_operation.activate()
  def exit(): Unit = query_operation.deactivate()
}
