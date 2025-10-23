/*  Title:      Tools/VSCode/src/sledgehammer_panel.scala
    Author:     Diana Korchmar
*/

package isabelle.vscode


import isabelle._

import java.io.{PrintStream, PrintWriter, FileWriter, OutputStream, File => JFile}

object Sledgehammer_Panel {
  def apply(server: Language_Server): Sledgehammer_Panel =
    new Sledgehammer_Panel(server)
}

class Sledgehammer_Panel private(server: Language_Server) {
  private val query_operation =
    new Query_Operation(server.editor, (), "sledgehammer", consume_status, consume_result)
  var current_purpose: Int = 1
  private var last_sendback_id: Option[Int] = None

  private val provers_history_option: String = "sledgehammer_provers_history"
  private val provers_history_delim: Char = '|'

  private var persistent_options: Options = Options.init()

  private def get_provers_history(): List[String] =
    Library.space_explode(provers_history_delim, persistent_options.string(provers_history_option)).filterNot(_.isEmpty)

  private def set_provers_history(new_history: String): Unit = {
    persistent_options = persistent_options.string.update(provers_history_option, new_history)
    persistent_options.save_prefs()
  }

  def send_provers_and_history(init: Boolean): Unit = {
    val provers = persistent_options.check_name("sledgehammer_provers").value
    val history = get_provers_history()
    server.channel.write(LSP.Sledgehammer_Provers_Response.apply(provers, history))
  }

  def add_provers_history(entry: String): Unit = {
    val current = get_provers_history()
    val history = (entry :: current.filter(_ != entry)).take(10)
    val history_str = history.mkString(provers_history_delim.toString)
    set_provers_history(history_str)
  }

  def handle_request(provers: String, isar: Boolean, try0: Boolean, purpose: Int): Unit = {
    val available_provers = persistent_options.string("sledgehammer_provers").split("\\s+").toSet
    val user_provers = provers.trim.split("\\s+").toSet
    val invalid = user_provers.diff(available_provers)
    if (invalid.nonEmpty) {
      server.channel.write(LSP.Sledgehammer_NoProver_Response.apply(invalid.toList))
      return
    }
    choose_purpose(List(provers, isar.toString, try0.toString), purpose)
    add_provers_history(provers)
  }

  def handle_sledgehammer_delete(entry: String): Unit = {
    val history = get_provers_history().filter(_ != entry)
    val history_str = history.mkString(provers_history_delim.toString)
    set_provers_history(history_str)
  }

  private def reload_persistent_options(): Unit = {
    persistent_options = Options.init()
  }

  private def consume_status(status: Query_Operation.Status): Unit = {
    val msg = status match {
      case Query_Operation.Status.waiting => "Warte auf Kontext..."
      case Query_Operation.Status.running => "Sledgehammer läuft..."
      case Query_Operation.Status.finished => "Beendet"
    }
    if (msg.nonEmpty) server.channel.write(LSP.Sledgehammer_Status_Response(msg))
  }

  private def extractSendbackId(body: List[XML.Elem]): Option[Int] = {
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
    val lastNewline = text.substring(0, offset).lastIndexOf('\n')
    if (lastNewline >= 0) offset - lastNewline - 1 else offset
  }

  private def resolvePosition(snapshot: Document.Snapshot, sendbackId: Int): Option[(String, Int, Int)] = {
    snapshot.node.commands.find(_.id == sendbackId).flatMap { command =>
      snapshot.node.command_iterator().find(_._1 == command).map {
        case (_, start_offset) =>
          val end_offset = start_offset + command.length // Hier nehmen wir das Ende des Command!
          val text = snapshot.node.source
          val line = count_lines(text, end_offset)
          val column = count_column(text, end_offset)
          val uri = Url.print_file(new java.io.File(snapshot.node_name.node))
          (uri, line, column)
      }
    }
  }

  private def query_position_from_sendback(snapshot: Document.Snapshot, sendbackId: Int): Option[(String, Int, Int)] = {
    val node = snapshot.node
    val iterator = node.command_iterator().toList

    iterator.find(_._1.id == sendbackId).map { case (command, start_offset) =>
      val text = node.source
      val line = count_lines(text, start_offset)
      val column = count_column(text, start_offset)
      val uri = Url.print_file(new java.io.File(snapshot.node_name.node))

      val snippet = text.substring(start_offset, (start_offset + command.length).min(text.length)).replace("\n", "\\n")

      (uri, line, column)
    }
  }

  private def consume_result(snapshot: Document.Snapshot, results: Command.Results, body: List[XML.Elem]): Unit = {
    val xmlString = body.map(XML.string_of_tree).mkString

    if (xmlString.contains("Done")) {
      val sendbackIdOpt = extractSendbackId(body)
      last_sendback_id = sendbackIdOpt

      val position = sendbackIdOpt.flatMap(id => resolvePosition(snapshot, id))
        .getOrElse(("unknown", 0, 0))

      val query_position = sendbackIdOpt.flatMap(id => query_position_from_sendback(snapshot, id))
        .getOrElse(("unknown", 0, 0))

      val text = snapshot.node.source

      val resultJson = JSON.Object(
        "content" -> xmlString,
        "position" -> JSON.Object(
          "uri" -> position._1,
          "line" -> position._2,
          "character" -> position._3
        ),
        "sendbackId" -> sendbackIdOpt.getOrElse(-1),
        "state_location" -> JSON.Object(
          "uri" -> query_position._1,
          "line" -> query_position._2,
          "character" -> query_position._3)
      )

      server.channel.write(LSP.Sledgehammer_Apply_Response(resultJson))
    }
  }

  def choose_purpose(args: List[String], purpose: Int): Unit = {
    current_purpose = purpose
    purpose match {
      case 1 =>
        server.resources.get_caret() match {
          case Some(caret) =>
            val snapshot = server.resources.snapshot(caret.model)
            val uri = Url.print_file(caret.file)
            query_operation.apply_query(args)
          case None =>
            server.channel.write(LSP.Sledgehammer_NoProof_Response())
        }

      case 2 =>
        locate()

      case 3 =>
        insert_query()

      case _ =>
    }
  }

  def locate(): Unit = {
    for {
      sendbackId <- last_sendback_id
      caret <- server.resources.get_caret()
      snapshot = server.resources.snapshot(caret.model)
      query_position <- query_position_from_sendback(snapshot, sendbackId)
    } {
      val json = JSON.Object(
        "position" -> JSON.Object(
          "uri" -> query_position._1,
          "line" -> query_position._2,
          "character" -> query_position._3
        )
      )
      server.channel.write(LSP.Sledgehammer_Locate_Response(json))
    }
  }

  def insert_query(): Unit = {
    last_sendback_id match {
      case Some(sendbackId) =>
        val models = server.resources.get_models()
        val modelOpt = models.find { model =>
          val snapshot = server.resources.snapshot(model)
          val contains = snapshot.node.commands.exists(_.id == sendbackId)
          contains
        }

        modelOpt match {
          case Some(model) =>
            val snapshot = server.resources.snapshot(model)
            resolvePosition(snapshot, sendbackId) match {
              case Some((uri, line, col)) =>
                val json = JSON.Object(
                  "position" -> JSON.Object(
                    "uri" -> uri,
                    "line" -> line,
                    "character" -> col
                  )
                )
                server.channel.write(LSP.Sledgehammer_InsertPosition_Response(json))
              case None =>
            }
          case None =>
        }
      case None =>
    }
  }

  def cancel_query(): Unit = query_operation.cancel_query()
  def locate_query(): Unit = query_operation.locate_query()
  def init(): Unit = query_operation.activate()
  def exit(): Unit = query_operation.deactivate()
}
