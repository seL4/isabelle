/*  Title:      Tools/VSCode/src/lsp.scala
    Author:     Makarius

Message formats for Language Server Protocol, with adhoc PIDE extensions.
See https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}


object LSP {
  /* abstract message */

  object Message {
    val empty: JSON.Object.T = JSON.Object("jsonrpc" -> "2.0")

    def log(prefix: String, json: JSON.T, logger: Logger, verbose: Boolean): Unit = {
      val header =
        json match {
          case JSON.Object(obj) => obj -- (obj.keySet - "method" - "id")
          case _ => JSON.Object.empty
        }
      if (verbose || header.isEmpty) logger(prefix + "\n" + JSON.Format(json))
      else logger(prefix + " " + JSON.Format(header))
    }
  }


  /* notification */

  object Notification {
    def apply(method: String, params: JSON.T): JSON.T =
      Message.empty + ("method" -> method) + ("params" -> params)

    def unapply(json: JSON.T): Option[(String, Option[JSON.T])] =
      for {
        method <- JSON.string(json, "method")
        params = JSON.value(json, "params")
      } yield (method, params)
  }

  class Notification0(name: String) {
    def unapply(json: JSON.T): Option[Unit] =
      json match {
        case Notification(method, _) if method == name => Some(())
        case _ => None
      }
  }


  /* request message */

  object Id {
    def empty: Id = Id("")
  }

  sealed case class Id(id: Any) {
    require(
      id.isInstanceOf[Int] ||
      id.isInstanceOf[Long] ||
      id.isInstanceOf[Double] ||
      id.isInstanceOf[String], "bad id type")

    override def toString: String = id.toString
  }

  object RequestMessage {
    def apply(id: Id, method: String, params: JSON.T): JSON.T =
      Message.empty + ("id" -> id.id) + ("method" -> method) + ("params" -> params)

    def unapply(json: JSON.T): Option[(Id, String, Option[JSON.T])] =
      for {
        id <- JSON.long(json, "id") orElse JSON.double(json, "id") orElse JSON.string(json, "id")
        method <- JSON.string(json, "method")
        params = JSON.value(json, "params")
      } yield (Id(id), method, params)
  }

  class Request0(name: String) {
    def unapply(json: JSON.T): Option[Id] =
      json match {
        case RequestMessage(id, method, _) if method == name => Some(id)
        case _ => None
      }
  }

  class RequestTextDocumentPosition(name: String) {
    def unapply(json: JSON.T): Option[(Id, Line.Node_Position)] =
      json match {
        case RequestMessage(id, method, Some(TextDocumentPosition(node_pos))) if method == name =>
          Some((id, node_pos))
        case _ => None
      }
  }


  /* response message */

  object ResponseMessage {
    def apply(id: Id, result: Option[JSON.T] = None, error: Option[ResponseError] = None): JSON.T =
      Message.empty + ("id" -> id.id) ++
        JSON.optional("result" -> result) ++
        JSON.optional("error" -> error.map(_.json))

    def strict(id: Id, result: Option[JSON.T] = None, error: String = ""): JSON.T =
      if (error == "") apply(id, result = result)
      else apply(id, error = Some(ResponseError(code = ErrorCodes.jsonrpcReservedErrorRangeEnd, message = error)))

    def is_empty(json: JSON.T): Boolean =
      JSON.string(json, "id") == Some("") && JSON.value(json, "result").isDefined
  }

  sealed case class ResponseError(code: Int, message: String, data: Option[JSON.T] = None) {
    def json: JSON.T =
      JSON.Object("code" -> code, "message" -> message) ++ JSON.optional("data" -> data)
  }

  object ErrorCodes {
    val ParseError = -32700
    val InvalidRequest = -32600
    val MethodNotFound = -32601
    val InvalidParams = -32602
    val InternalError = -32603

    val jsonrpcReservedErrorRangeStart = -32099
    val ServerNotInitialized = -32002
    val UnknownErrorCode = -32001
    val jsonrpcReservedErrorRangeEnd = -32000

    val lspReservedErrorRangeStart = -32899
    val RequestFailed = -32803
    val ServerCancelled = -32802
    val ContentModified = -32801
    val RequestCancelled = -32800
    val lspReservedErrorRangeEnd = -32800
  }
  

  /* init and exit */

  object Initialize extends Request0("initialize") {
    def reply(id: Id, error: String): JSON.T =
      ResponseMessage.strict(
        id, Some(JSON.Object("capabilities" -> ServerCapabilities.json)), error)
  }

  object ServerCapabilities {
    val json: JSON.T =
      JSON.Object(
        "textDocumentSync" -> 2,
        "completionProvider" -> JSON.Object(
          "resolveProvider" -> false,
          "triggerCharacters" ->
            (Symbol.symbols.entries.flatMap(_.abbrevs).flatMap(_.toList).map(_.toString)
            ++ Symbol.symbols.entries.map(_.name).flatMap(_.toList).map(_.toString)).distinct
        ),
        "hoverProvider" -> true,
        "definitionProvider" -> true,
        "documentHighlightProvider" -> true,
        "codeActionProvider" -> true)
  }

  object Initialized extends Notification0("initialized")

  object Shutdown extends Request0("shutdown") {
    def reply(id: Id, error: String): JSON.T =
      ResponseMessage.strict(id, Some("OK"), error)
  }

  object Exit extends Notification0("exit")


  /* document positions */

  object Position {
    def apply(pos: Line.Position): JSON.T =
      JSON.Object("line" -> pos.line, "character" -> pos.column)

    def unapply(json: JSON.T): Option[Line.Position] =
      for {
        line <- JSON.int(json, "line")
        column <- JSON.int(json, "character")
      } yield Line.Position(line, column)
  }

  object Range {
    def compact(range: Line.Range): List[Int] =
      List(range.start.line, range.start.column, range.stop.line, range.stop.column)

    def apply(range: Line.Range): JSON.T =
      JSON.Object("start" -> Position(range.start), "end" -> Position(range.stop))

    def unapply(json: JSON.T): Option[Line.Range] =
      (JSON.value(json, "start"), JSON.value(json, "end")) match {
        case (Some(Position(start)), Some(Position(stop))) => Some(Line.Range(start, stop))
        case _ => None
      }
  }

  object Location {
    def apply(loc: Line.Node_Range): JSON.T =
      JSON.Object("uri" -> Url.print_file_name(loc.name), "range" -> Range(loc.range))

    def unapply(json: JSON.T): Option[Line.Node_Range] =
      for {
        uri <- JSON.string(json, "uri")
        if Url.is_wellformed_file(uri)
        range_json <- JSON.value(json, "range")
        range <- Range.unapply(range_json)
      } yield Line.Node_Range(Url.absolute_file_name(uri), range)
  }

  object TextDocumentPosition {
    def unapply(json: JSON.T): Option[Line.Node_Position] =
      for {
        doc <- JSON.value(json, "textDocument")
        uri <- JSON.string(doc, "uri")
        if Url.is_wellformed_file(uri)
        pos_json <- JSON.value(json, "position")
        pos <- Position.unapply(pos_json)
      } yield Line.Node_Position(Url.absolute_file_name(uri), pos)
  }


  /* marked strings */

  sealed case class MarkedString(text: String, language: String = "plaintext") {
    def json: JSON.T = JSON.Object("language" -> language, "value" -> text)
  }

  object MarkedStrings {
    def json(msgs: List[MarkedString]): Option[JSON.T] =
      msgs match {
        case Nil => None
        case List(msg) => Some(msg.json)
        case _ => Some(msgs.map(_.json))
      }
  }


  /* diagnostic messages */

  object MessageType {
    val Error = 1
    val Warning = 2
    val Info = 3
    val Log = 4
  }

  object DisplayMessage {
    def apply(message_type: Int, message: String, show: Boolean): JSON.T =
      Notification(if (show) "window/showMessage" else "window/logMessage",
        JSON.Object("type" -> message_type, "message" -> message))
  }


  /* commands */

  sealed case class Command(title: String, command: String, arguments: List[JSON.T] = Nil) {
    def json: JSON.T =
      JSON.Object("title" -> title, "command" -> command, "arguments" -> arguments)
  }


  /* document edits */

  object DidOpenTextDocument {
    def unapply(json: JSON.T): Option[(JFile, String, Long, String)] =
      json match {
        case Notification("textDocument/didOpen", Some(params)) =>
          for {
            doc <- JSON.value(params, "textDocument")
            uri <- JSON.string(doc, "uri")
            if Url.is_wellformed_file(uri)
            lang <- JSON.string(doc, "languageId")
            version <- JSON.long(doc, "version")
            text <- JSON.string(doc, "text")
          } yield (Url.absolute_file(uri), lang, version, text)
        case _ => None
      }
  }


  sealed case class TextDocumentChange(range: Option[Line.Range], text: String)

  object DidChangeTextDocument {
    def unapply_change(json: JSON.T): Option[TextDocumentChange] =
      for { text <- JSON.string(json, "text") }
      yield TextDocumentChange(JSON.value(json, "range", Range.unapply), text)

    def unapply(json: JSON.T): Option[(JFile, Long, List[TextDocumentChange])] =
      json match {
        case Notification("textDocument/didChange", Some(params)) =>
          for {
            doc <- JSON.value(params, "textDocument")
            uri <- JSON.string(doc, "uri")
            if Url.is_wellformed_file(uri)
            version <- JSON.long(doc, "version")
            changes <- JSON.list(params, "contentChanges", unapply_change)
          } yield (Url.absolute_file(uri), version, changes)
        case _ => None
      }
  }

  class TextDocumentNotification(name: String) {
    def unapply(json: JSON.T): Option[JFile] =
      json match {
        case Notification(method, Some(params)) if method == name =>
          for {
            doc <- JSON.value(params, "textDocument")
            uri <- JSON.string(doc, "uri")
            if Url.is_wellformed_file(uri)
          } yield Url.absolute_file(uri)
        case _ => None
      }
  }

  object DidCloseTextDocument extends TextDocumentNotification("textDocument/didClose")
  object DidSaveTextDocument extends TextDocumentNotification("textDocument/didSave")


  /* workspace edits */

  sealed case class TextEdit(range: Line.Range, new_text: String) {
    def json: JSON.T = JSON.Object("range" -> Range(range), "newText" -> new_text)
  }

  sealed case class TextDocumentEdit(file: JFile, version: Option[Long], edits: List[TextEdit]) {
    def json: JSON.T =
      JSON.Object(
        "textDocument" -> (
          JSON.Object("uri" -> Url.print_file(file)) ++
          JSON.optional("version" -> version)
        ),
        "edits" -> edits.map(_.json)
      )
  }

  object WorkspaceEdit {
    def apply(edits: List[TextDocumentEdit]): JSON.T =
      JSON.Object("documentChanges" -> edits.map(_.json))
  }

  object ApplyWorkspaceEdit {
    def apply(edits: List[TextDocumentEdit]): JSON.T =
      RequestMessage(Id.empty, "workspace/applyEdit",
        JSON.Object("edit" -> WorkspaceEdit(edits))
      )
  }


  /* completion */
  
  object CompletionItemKind {
    val Text = 1;
    val Method = 2;
    val Function = 3;
    val Constructor = 4;
    val Field = 5;
    val Variable = 6;
    val Class = 7;
    val Interface = 8;
    val Module = 9;
    val Property = 10;
    val Unit = 11;
    val Value = 12;
    val Enum = 13;
    val Keyword = 14;
    val Snippet = 15;
    val Color = 16;
    val File = 17;
    val Reference = 18;
    val Folder = 19;
    val EnumMember = 20;
    val Constant = 21;
    val Struct = 22;
    val Event = 23;
    val Operator = 24;
    val TypeParameter = 25;
  }

  sealed case class CompletionItem(
    label: String,
    kind: Option[Int] = None,
    detail: Option[String] = None,
    documentation: Option[String] = None,
    filter_text: Option[String] = None,
    commit_characters: Option[List[String]] = None,
    text: Option[String] = None,
    range: Option[Line.Range] = None,
    command: Option[Command] = None
  ) {
    def json: JSON.T =
      JSON.Object("label" -> label) ++
      JSON.optional("kind" -> kind) ++
      JSON.optional("detail" -> detail) ++
      JSON.optional("documentation" -> documentation) ++
      JSON.optional("filterText" -> filter_text) ++
      JSON.optional("textEdit" -> range.map(r => TextEdit(range = r, new_text = text.getOrElse(label)).json)) ++
      JSON.optional("commitCharacters" -> commit_characters) ++
      JSON.optional("command" -> command.map(_.json))
  }

  object Completion extends RequestTextDocumentPosition("textDocument/completion") {
    def reply(id: Id, result: List[CompletionItem]): JSON.T =
      ResponseMessage(id, Some(result.map(_.json)))
  }


  /* spell checker */

  object Include_Word extends Notification0("PIDE/include_word") {
    val command = Command("Include word", "isabelle.include-word")
  }

  object Include_Word_Permanently extends Notification0("PIDE/include_word_permanently") {
    val command = Command("Include word permanently", "isabelle.include-word-permanently")
  }

  object Exclude_Word extends Notification0("PIDE/exclude_word") {
    val command = Command("Exclude word", "isabelle.exclude-word")
  }

  object Exclude_Word_Permanently extends Notification0("PIDE/exclude_word_permanently") {
    val command = Command("Exclude word permanently", "isabelle.exclude-word-permanently")
  }

  object Reset_Words extends Notification0("PIDE/reset_words") {
    val command = Command("Reset non-permanent words", "isabelle.reset-words")
  }


  /* hover request */

  object Hover extends RequestTextDocumentPosition("textDocument/hover") {
    def reply(id: Id, result: Option[(Line.Range, List[MarkedString])]): JSON.T = {
      val res =
        result match {
          case Some((range, contents)) =>
            JSON.Object(
              "contents" -> MarkedStrings.json(contents).getOrElse(Nil),
              "range" -> Range(range))
          case None => JSON.Object("contents" -> Nil)
        }
      ResponseMessage(id, Some(res))
    }
  }


  /* goto definition request */

  object GotoDefinition extends RequestTextDocumentPosition("textDocument/definition") {
    def reply(id: Id, result: List[Line.Node_Range]): JSON.T =
      ResponseMessage(id, Some(result.map(Location.apply)))
  }


  /* document highlights request */

  object DocumentHighlight {
    def text(range: Line.Range): DocumentHighlight = DocumentHighlight(range, Some(1))
    def read(range: Line.Range): DocumentHighlight = DocumentHighlight(range, Some(2))
    def write(range: Line.Range): DocumentHighlight = DocumentHighlight(range, Some(3))
  }

  sealed case class DocumentHighlight(range: Line.Range, kind: Option[Int] = None) {
    def json: JSON.T =
      kind match {
        case None => JSON.Object("range" -> Range(range))
        case Some(k) => JSON.Object("range" -> Range(range), "kind" -> k)
      }
  }

  object DocumentHighlights extends RequestTextDocumentPosition("textDocument/documentHighlight") {
    def reply(id: Id, result: List[DocumentHighlight]): JSON.T =
      ResponseMessage(id, Some(result.map(_.json)))
  }


  /* diagnostics */

  sealed case class Diagnostic(
    range: Line.Range,
    message: String,
    severity: Option[Int] = None,
    code: Option[Int] = None,
    source: Option[String] = None
  ) {
    def json: JSON.T =
      Message.empty + ("range" -> Range(range)) + ("message" -> message) ++
      JSON.optional("severity" -> severity) ++
      JSON.optional("code" -> code) ++
      JSON.optional("source" -> source)
  }

  object DiagnosticSeverity {
    val Error = 1
    val Warning = 2
    val Information = 3
    val Hint = 4
  }

  object PublishDiagnostics {
    def apply(file: JFile, diagnostics: List[Diagnostic]): JSON.T =
      Notification("textDocument/publishDiagnostics",
        JSON.Object("uri" -> Url.print_file(file), "diagnostics" -> diagnostics.map(_.json)))
  }


  /* code actions */

  sealed case class CodeAction(title: String, edits: List[TextDocumentEdit]) {
    def json: JSON.T =
      JSON.Object("title" -> title, "edit" -> WorkspaceEdit(edits))
  }

  object CodeActionRequest {
    def unapply(json: JSON.T): Option[(Id, JFile, Line.Range)] =
      json match {
        case RequestMessage(id, "textDocument/codeAction", Some(params)) =>
          for {
            doc <- JSON.value(params, "textDocument")
            uri <- JSON.string(doc, "uri")
            if Url.is_wellformed_file(uri)
            range_json <- JSON.value(params, "range")
            range <- Range.unapply(range_json)
          } yield (id, Url.absolute_file(uri), range)
        case _ => None
      }

    def reply(id: Id, actions: List[CodeAction]): JSON.T =
      ResponseMessage(id, Some(actions.map(_.json)))
  }


  /* decorations */

  sealed case class Decoration_Options(range: Line.Range, hover_message: List[MarkedString]) {
    def json: JSON.T =
      JSON.Object("range" -> Range.compact(range)) ++
      JSON.optional("hover_message" -> MarkedStrings.json(hover_message))
  }

  type Decoration_List = List[(String, List[Decoration_Options])]

  sealed case class Decoration(decorations: Decoration_List) {
    def json_entries: JSON.T =
      decorations.map(decoration => JSON.Object(
        "type" -> decoration._1,
        "content" -> decoration._2.map(_.json))
      )

    def json(file: JFile): JSON.T =
      Notification("PIDE/decoration",
        JSON.Object(
          "uri" -> Url.print_file(file),
          "entries" -> json_entries
        )
      )
  }
  
  object Decoration_Request {
    def unapply(json: JSON.T): Option[JFile] =
      json match {
        case Notification("PIDE/decoration_request", Some(params)) =>
          for {
            uri <- JSON.string(params, "uri")
            if Url.is_wellformed_file(uri)
          } yield Url.absolute_file(uri)
        case _ => None
      }
  }


  /* caret update: bidirectional */

  object Caret_Update {
    def apply(node_pos: Line.Node_Position, focus: Boolean): JSON.T =
      Notification("PIDE/caret_update",
        JSON.Object(
          "uri" -> Url.print_file_name(node_pos.name),
          "line" -> node_pos.pos.line,
          "character" -> node_pos.pos.column,
          "focus" -> focus))

    def unapply(json: JSON.T): Option[Option[(JFile, Line.Position)]] =
      json match {
        case Notification("PIDE/caret_update", Some(params)) =>
          val caret =
            for {
              uri <- JSON.string(params, "uri")
              if Url.is_wellformed_file(uri)
              pos <- Position.unapply(params)
            } yield (Url.absolute_file(uri), pos)
          Some(caret)
        case _ => None
      }
  }


  /* dynamic output */

  object Dynamic_Output {
    def apply(content: String, decoration: Option[Decoration] = None): JSON.T =
      Notification("PIDE/dynamic_output",
        JSON.Object("content" -> content) ++
        JSON.optional("decorations" -> decoration.map(_.json_entries))
      )
  }

  object Output_Set_Margin {
    def unapply(json: JSON.T): Option[Double] =
      json match {
        case Notification("PIDE/output_set_margin", Some(params)) =>
          JSON.double(params, "margin")
        case _ => None
      }
  }


  /* state output */

  object State_Output {
    def apply(
       id: Counter.ID,
       content: String,
       auto_update: Boolean,
       decorations: Option[Decoration] = None
    ): JSON.T =
      Notification("PIDE/state_output",
        JSON.Object("id" -> id, "content" -> content, "auto_update" -> auto_update) ++
        JSON.optional("decorations" -> decorations.map(_.json_entries))
      )
  }

  class State_Id_Notification(name: String) {
    def unapply(json: JSON.T): Option[Counter.ID] =
      json match {
        case Notification(method, Some(params)) if method == name => JSON.long(params, "id")
        case _ => None
      }
  }

  object State_Init extends Request0("PIDE/state_init") {
    def reply(id: Id, state_id: Counter.ID): JSON.T =
      ResponseMessage(id, Some(JSON.Object("state_id" -> state_id)))
  }

  object State_Exit extends State_Id_Notification("PIDE/state_exit")
  object State_Locate extends State_Id_Notification("PIDE/state_locate")
  object State_Update extends State_Id_Notification("PIDE/state_update")

  object State_Auto_Update {
    def unapply(json: JSON.T): Option[(Counter.ID, Boolean)] =
      json match {
        case Notification("PIDE/state_auto_update", Some(params)) =>
          for {
            id <- JSON.long(params, "id")
            enabled <- JSON.bool(params, "enabled")
          } yield (id, enabled)
        case _ => None
      }
  }

  object State_Set_Margin {
    def unapply(json: JSON.T): Option[(Counter.ID, Double)] =
      json match {
        case Notification("PIDE/state_set_margin", Some(params)) =>
          for {
            id <- JSON.long(params, "id")
            margin <- JSON.double(params, "margin")
          } yield (id, margin)
        case _ => None
      }
  }


  /* symbols */

  object Symbols_Request extends Request0("PIDE/symbols_request") {
    def reply(id: Id, symbols: Symbol.Symbols): JSON.T = {
      def json(symbol: Symbol.Entry): JSON.T =
        JSON.Object(
          "symbol" -> symbol.symbol,
          "name" -> symbol.name,
          "argument" -> symbol.argument.toString,
        ) ++
          JSON.optional("code", symbol.code) ++
          JSON.optional("font", symbol.font) ++
          JSON.Object(
            "groups" -> symbol.groups,
            "abbrevs" -> symbol.abbrevs,
          )

      ResponseMessage(id, Some(symbols.entries.map(s => json(s))))
    }
  }
  
  object Symbols_Convert_Request {
    def unapply(json: JSON.T): Option[(Id, String, Boolean)] =
      json match {
        case RequestMessage(id, "PIDE/symbols_convert_request", Some(params)) =>
          for {
            s <- JSON.string(params, "text")
            unicode <- JSON.bool(params, "unicode")
          } yield (id, s, unicode)
        case _ => None
      }

    def reply(id: Id, new_string: String): JSON.T =
      ResponseMessage(id, Some(JSON.Object("text" -> new_string)))
  }


  /* preview */

  object Preview_Request {
    def unapply(json: JSON.T): Option[(JFile, Int)] =
      json match {
        case Notification("PIDE/preview_request", Some(params)) =>
          for {
            uri <- JSON.string(params, "uri")
            if Url.is_wellformed_file(uri)
            column <- JSON.int(params, "column")
          } yield (Url.absolute_file(uri), column)
        case _ => None
      }
  }

  object Preview_Response {
    def apply(file: JFile, column: Int, label: String, content: String): JSON.T =
      Notification("PIDE/preview_response",
        JSON.Object(
          "uri" -> Url.print_file(file),
          "column" -> column,
          "label" -> label,
          "content" -> content))
  }
}
