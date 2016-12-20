/*  Title:      Tools/VSCode/src/protocol.scala
    Author:     Makarius

Message formats for Language Server Protocol 2.0, see
https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md
*/

package isabelle.vscode


import isabelle._


object Protocol
{
  /* abstract message */

  object Message
  {
    val empty: Map[String, JSON.T] = Map("jsonrpc" -> "2.0")
  }


  /* notification */

  object Notification
  {
    def apply(method: String, params: JSON.T): JSON.T =
      Message.empty + ("method" -> method) + ("params" -> params)

    def unapply(json: JSON.T): Option[(String, Option[JSON.T])] =
      for {
        method <- JSON.string(json, "method")
        params = JSON.value(json, "params")
      } yield (method, params)
  }

  class Notification0(name: String)
  {
    def unapply(json: JSON.T): Option[Unit] =
      json match {
        case Notification(method, _) if method == name => Some(())
        case _ => None
      }
  }


  /* request message */

  sealed case class Id(id: Any)
  {
    require(
      id.isInstanceOf[Int] ||
      id.isInstanceOf[Long] ||
      id.isInstanceOf[Double] ||
      id.isInstanceOf[String])

    override def toString: String = id.toString
  }

  object RequestMessage
  {
    def apply(id: Id, method: String, params: JSON.T): JSON.T =
      Message.empty + ("id" -> id.id) + ("method" -> method) + ("params" -> params)

    def unapply(json: JSON.T): Option[(Id, String, Option[JSON.T])] =
      for {
        id <- JSON.long(json, "id") orElse JSON.double(json, "id") orElse JSON.string(json, "id")
        method <- JSON.string(json, "method")
        params = JSON.value(json, "params")
      } yield (Id(id), method, params)
  }

  class Request0(name: String)
  {
    def unapply(json: JSON.T): Option[Id] =
      json match {
        case RequestMessage(id, method, _) if method == name => Some(id)
        case _ => None
      }
  }


  /* response message */

  object ResponseMessage
  {
    def apply(id: Id, result: Option[JSON.T] = None, error: Option[ResponseError] = None): JSON.T =
      Message.empty + ("id" -> id.id) ++
      (result match { case Some(x) => Map("result" -> x) case None => Map.empty }) ++
      (error match { case Some(x) => Map("error" -> x.json) case None => Map.empty })

    def strict(id: Id, result: Option[JSON.T] = None, error: String = ""): JSON.T =
      if (error == "") apply(id, result = result)
      else apply(id, error = Some(ResponseError(code = ErrorCodes.serverErrorEnd, message = error)))
  }

  sealed case class ResponseError(code: Int, message: String, data: Option[JSON.T] = None)
  {
    def json: JSON.T =
      Map("code" -> code, "message" -> message) ++
      (data match { case Some(x) => Map("data" -> x) case None => Map.empty })
  }

  object ErrorCodes
  {
    val ParseError = -32700
    val InvalidRequest = -32600
    val MethodNotFound = -32601
    val InvalidParams = -32602
    val InternalError = -32603
    val serverErrorStart = -32099
    val serverErrorEnd = -32000
  }


  /* init and exit */

  object Initialize extends Request0("initialize")
  {
    def reply(id: Id, error: String): JSON.T =
      ResponseMessage.strict(id, Some(Map("capabilities" -> ServerCapabilities.json)), error)
  }

  object ServerCapabilities
  {
    val json: JSON.T =
      Map("textDocumentSync" -> 1, "hoverProvider" -> true)
  }

  object Shutdown extends Request0("shutdown")
  {
    def reply(id: Id, error: String): JSON.T =
      ResponseMessage.strict(id, Some("OK"), error)
  }

  object Exit extends Notification0("exit")


  /* document positions */

  object Position
  {
    def apply(pos: Line.Position): JSON.T =
      Map("line" -> pos.line, "character" -> pos.column)

    def unapply(json: JSON.T): Option[Line.Position] =
      for {
        line <- JSON.int(json, "line")
        column <- JSON.int(json, "character")
      } yield Line.Position(line, column)
  }

  object Range
  {
    def apply(range: Line.Range): JSON.T =
      Map("start" -> Position(range.start), "end" -> Position(range.stop))

    def unapply(json: JSON.T): Option[Line.Range] =
      (JSON.value(json, "start"), JSON.value(json, "end")) match {
        case (Some(Position(start)), Some(Position(stop))) => Some(Line.Range(start, stop))
        case _ => None
      }
  }

  object Location
  {
    def apply(uri: String, range: Line.Range): JSON.T =
      Map("uri" -> uri, "range" -> Range(range))

    def unapply(json: JSON.T): Option[(String, Line.Range)] =
      for {
        uri <- JSON.string(json, "uri")
        range_json <- JSON.value(json, "range")
        range <- Range.unapply(range_json)
      } yield (uri, range)
  }

  object TextDocumentPosition
  {
    def unapply(json: JSON.T): Option[(String, Line.Position)] =
      for {
        doc <- JSON.value(json, "textDocument")
        uri <- JSON.string(doc, "uri")
        pos_json <- JSON.value(json, "position")
        pos <- Position.unapply(pos_json)
      } yield (uri, pos)
  }


  /* diagnostic messages */

  object MessageType
  {
    val Error = 1
    val Warning = 2
    val Info = 3
    val Log = 4
  }

  object DisplayMessage
  {
    def apply(message_type: Int, message: String, show: Boolean = true): JSON.T =
      Notification(if (show) "window/showMessage" else "window/logMessage",
        Map("type" -> message_type, "message" -> message))
  }


  /* document edits */

  object DidOpenTextDocument
  {
    def unapply(json: JSON.T): Option[(String, String, Long, String)] =
      json match {
        case Notification("textDocument/didOpen", Some(params)) =>
          for {
            doc <- JSON.value(params, "textDocument")
            uri <- JSON.string(doc, "uri")
            lang <- JSON.string(doc, "languageId")
            version <- JSON.long(doc, "version")
            text <- JSON.string(doc, "text")
          } yield (uri, lang, version, text)
        case _ => None
      }
  }


  sealed abstract class TextDocumentContentChange
  case class TextDocumentContent(text: String) extends TextDocumentContentChange
  case class TextDocumentChange(range: Line.Range, range_length: Int, text: String)
    extends TextDocumentContentChange

  object TextDocumentContentChange
  {
    def unapply(json: JSON.T): Option[TextDocumentContentChange] =
      for { text <- JSON.string(json, "text") }
      yield {
        (JSON.value(json, "range"), JSON.int(json, "rangeLength")) match {
          case (Some(Range(range)), Some(range_length)) =>
            TextDocumentChange(range, range_length, text)
          case _ => TextDocumentContent(text)
        }
      }
  }

  object DidChangeTextDocument
  {
    def unapply(json: JSON.T): Option[(String, Long, List[TextDocumentContentChange])] =
      json match {
        case Notification("textDocument/didChange", Some(params)) =>
          for {
            doc <- JSON.value(params, "textDocument")
            uri <- JSON.string(doc, "uri")
            version <- JSON.long(doc, "version")
            changes <- JSON.array(params, "contentChanges", TextDocumentContentChange.unapply _)
          } yield (uri, version, changes)
        case _ => None
      }
  }

  class TextDocumentNotification(name: String)
  {
    def unapply(json: JSON.T): Option[String] =
      json match {
        case Notification(method, Some(params)) if method == name =>
          for {
            doc <- JSON.value(params, "textDocument")
            uri <- JSON.string(doc, "uri")
          } yield uri
        case _ => None
      }
  }

  object DidCloseTextDocument extends TextDocumentNotification("textDocument/didClose")
  object DidSaveTextDocument extends TextDocumentNotification("textDocument/didSave")


  /* hover request */

  object Hover
  {
    def unapply(json: JSON.T): Option[(Id, String, Line.Position)] =
      json match {
        case RequestMessage(id, "textDocument/hover", Some(TextDocumentPosition(uri, pos))) =>
          Some((id, uri, pos))
        case _ => None
      }

    def reply(id: Id, result: Option[(Line.Range, List[String])]): JSON.T =
    {
      val res =
        result match {
          case Some((range, contents)) => Map("contents" -> contents, "range" -> Range(range))
          case None => Map("contents" -> Nil)
        }
      ResponseMessage(id, Some(res))
    }
  }
}
