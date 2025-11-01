/*  Title:      Tools/VSCode/src/vscode_sledgehammer.scala
    Author:     Diana Korchmar, LMU Muenchen
    Author:     Makarius

Control panel for Sledgehammer.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}


class VSCode_Sledgehammer(server: Language_Server) {
  private val query_operation =
    new Query_Operation(server.editor, (), "sledgehammer", consume_status, consume_output)

  private var last_sendback_id: Option[Int] = None

  def send_provers(): Unit = {
    val provers = server.options.string("sledgehammer_provers")
    server.channel.write(LSP.Sledgehammer_Provers_Response.apply(provers))
  }

  def handle_request(provers: String, isar: Boolean, try0: Boolean): Unit =
    server.resources.get_caret() match {
      case Some(caret) =>
        val snapshot = server.resources.snapshot(caret.model)
        val uri = Url.print_file(caret.file)
        server.editor.send_dispatcher {
          query_operation.apply_query(List(provers, isar.toString, try0.toString))
        }
      case None => server.channel.write(LSP.Sledgehammer_No_Proof_Response())
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

  private def extract_sendback_id(body: List[XML.Elem]): Option[Int] = {
    def traverse(tree: XML.Tree): Option[Int] = tree match {
      case XML.Elem(markup, body) if markup.name == "sendback" =>
        markup.properties.find(_._1 == "id").flatMap {
          case (_, id_str) => scala.util.Try(id_str.toInt).toOption
        }.orElse(body.view.flatMap(traverse).headOption)

      case XML.Elem(_, body) =>
        body.view.flatMap(traverse).headOption

      case _ => None
    }
    body.view.flatMap(traverse).headOption
  }

  private def count_lines(text: String, offset: Int): Int =
    text.substring(0, offset).count(_ == '\n')

  private def count_column(text: String, offset: Int): Int = {
    val last_newline = text.substring(0, offset).lastIndexOf('\n')
    if (last_newline >= 0) offset - last_newline - 1 else offset
  }

  private def resolve_position(
    snapshot: Document.Snapshot,
    sendback_id: Int
  ): Option[(String, Int, Int)] = {
    snapshot.node.commands.find(_.id == sendback_id).flatMap { command =>
      snapshot.node.command_iterator().find(_._1 == command).map {
        case (_, start_offset) =>
          val end_offset = start_offset + command.length
          val text = snapshot.node.source
          val line = count_lines(text, end_offset)
          val column = count_column(text, end_offset)
          val uri = Url.print_file(new java.io.File(snapshot.node_name.node))
          (uri, line, column)
      }
    }
  }

  private def query_position_from_sendback(
    snapshot: Document.Snapshot,
    sendback_id: Int
  ): Option[(String, Int, Int)] = {
    val node = snapshot.node
    val iterator = node.command_iterator().toList

    iterator.find(_._1.id == sendback_id).map { case (command, start_offset) =>
      val text = node.source
      val line = count_lines(text, start_offset)
      val column = count_column(text, start_offset)
      val uri = Url.print_file(new java.io.File(snapshot.node_name.node))

      val snippet =
        text.substring(start_offset, (start_offset + command.length).min(text.length))
          .replace("\n", "\\n")

      (uri, line, column)
    }
  }

  private def consume_output(output: Editor.Output): Unit = {
    val snapshot = output.snapshot
    val body = output.messages

    val sendback_id_opt = extract_sendback_id(body)
    last_sendback_id = sendback_id_opt

    val position = sendback_id_opt.flatMap(id => resolve_position(snapshot, id))
      .getOrElse(("unknown", 0, 0))

    val query_position = sendback_id_opt.flatMap(id => query_position_from_sendback(snapshot, id))
      .getOrElse(("unknown", 0, 0))

    val json = JSON.Object(
      "content" -> XML.string_of_body(body),
      "position" -> JSON.Object(
        "uri" -> position._1,
        "line" -> position._2,
        "character" -> position._3
      ),
      "sendback_id" -> sendback_id_opt.getOrElse(-1),
      "state_location" -> JSON.Object(
        "uri" -> query_position._1,
        "line" -> query_position._2,
        "character" -> query_position._3)
    )
    server.channel.write(LSP.Sledgehammer_Output(json))
  }

  def insert(): Unit = {
    last_sendback_id match {
      case Some(sendback_id) =>
        val models = server.resources.get_models()
        val model_opt = models.find { model =>
          val snapshot = server.resources.snapshot(model)
          val contains = snapshot.node.commands.exists(_.id == sendback_id)
          contains
        }

        model_opt match {
          case Some(model) =>
            val snapshot = server.resources.snapshot(model)
            resolve_position(snapshot, sendback_id) match {
              case Some((uri, line, col)) =>
                val json = JSON.Object(
                  "position" -> JSON.Object(
                    "uri" -> uri,
                    "line" -> line,
                    "character" -> col
                  )
                )
                server.channel.write(LSP.Sledgehammer_Insert_Position_Response(json))
              case None =>
            }
          case None =>
        }
      case None =>
    }
  }

  def cancel(): Unit = server.editor.send_dispatcher { query_operation.cancel_query() }
  def locate(): Unit = server.editor.send_dispatcher { query_operation.locate_query() }
  def init(): Unit = query_operation.activate()
  def exit(): Unit = query_operation.deactivate()
}
