/*  Title:      Tools/VSCode/src/lsp.scala
    Author:     Makarius
    Author:     Thomas Lindae, TU Muenchen
    Author:     Diana Korchmar, LMU Muenchen

Message formats for Language Server Protocol, with adhoc PIDE extensions.
See https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md
*/

package isabelle.vscode


import isabelle._


object LSP {
  /* abstract message */

  object Message {
    val empty: JSON.Object.T = JSON.Object("jsonrpc" -> "2.0")

    def log(prefix: => String, json: JSON.T, logger: Logger, verbose: Boolean): Unit = {
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

    def unapply(json: JSON.T): Option[(String, JSON.T)] =
      for {
        method <- JSON.string(json, "method")
        params <- JSON.value(json, "params")
      } yield (method, params)
  }

  class Notification(val name: String)

  object Notification0 {
    def apply(method: String): JSON.T = Message.empty + ("method" -> method)

    def unapply(json: JSON.T): Option[String] = JSON.string(json, "method")
  }

  class Notification0(val name: String) {
    def apply(): JSON.T = Notification0(name)

    def unapply(json: JSON.T): Boolean = Notification0.unapply(json).contains(name)
  }


  /* request message */

  object Id {
    def empty: Id = Id("")

    def unapply(json: JSON.T): Option[Id] =
      for (i <- JSON.long(json, "id") orElse JSON.double(json, "id") orElse JSON.string(json, "id"))
      yield Id(i)
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

    def unapply(json: JSON.T): Option[(Id, String, JSON.T)] =
      json match {
        case Id(id) =>
          for {
            method <- JSON.string(json, "method")
            params <- JSON.value(json, "params")
          } yield (id, method, params)
        case _ => None
      }
  }

  class Request(val name: String)

  object RequestMessage0 {
    def apply(id: Id, method: String): JSON.T =
      Message.empty + ("id" -> id.id) + ("method" -> method)

    def unapply(json: JSON.T): Option[(Id, String)] =
      json match {
        case Id(id) => for (method <- JSON.string(json, "method")) yield (id, method)
        case _ => None
      }
  }

  class Request0(val name: String) {
    def apply(id: Id): JSON.T = RequestMessage0.apply(id, name)

    def unapply(json: JSON.T): Option[Id] =
      RequestMessage0.unapply(json).filter(_._2 == name).map(_._1)
  }

  class RequestTextDocumentPosition(name: String) extends Request(name) {
    def unapply(json: JSON.T): Option[(Id, Line.Node_Position)] =
      json match {
        case RequestMessage(id, method, TextDocumentPosition(node_pos)) if method == name =>
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
      else {
        apply(id, error =
          Some(ResponseError(code = ErrorCodes.jsonrpcReservedErrorRangeEnd, message = error)))
      }

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

    def expand(elems: List[Int]): Option[Line.Range] =
      elems match {
        case start_line :: start_column :: stop_line :: stop_column :: Nil =>
          val start = Line.Position(start_line, start_column)
          val stop = Line.Position(stop_line, stop_column)
          Some(Line.Range(start, stop))
        case _ => None
      }

    def apply(range: Line.Range): JSON.T =
      JSON.Object("start" -> Position(range.start), "end" -> Position(range.stop))

    def unapply(json: JSON.T): Option[Line.Range] =
      for {
        case Position(start) <- JSON.value(json, "start")
        case Position(stop) <- JSON.value(json, "end")
      } yield Line.Range(start, stop)
  }

  object Location {
    def apply(loc: Line.Node_Range): JSON.T =
      JSON.Object("uri" -> Url.print_file_name(loc.name), "range" -> Range(loc.range))

    def unapply(json: JSON.T): Option[Line.Node_Range] =
      for {
        uri <- JSON.string(json, "uri") if Url.is_wellformed_file(uri)
        case Range(range) <- JSON.value(json, "range")
      } yield Line.Node_Range(Url.absolute_file_name(uri), range)
  }

  object TextDocumentPosition {
    def unapply(json: JSON.T): Option[Line.Node_Position] =
      for {
        doc <- JSON.value(json, "textDocument")
        uri <- JSON.string(doc, "uri") if Url.is_wellformed_file(uri)
        pos_json <- JSON.value(json, "position")
        pos <- Position.unapply(pos_json)
      } yield Line.Node_Position(Url.absolute_file_name(uri), pos)
  }


  /* marked strings */

  object MarkedString {
    def unapply(json: JSON.T): Option[MarkedString] =
      json match {
        case JSON.Value.String(text) => Some(MarkedString(text))
        case _ =>
          for {
            text <- JSON.string(json, "value")
            language <- JSON.string_default(json, "language", "plaintext")
          } yield MarkedString(text, language)
      }
  }

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

    def unapply(json: JSON.T): Option[List[MarkedString]] =
      json match {
        case values: List[_] => JSON.Value.List.unapply(values, MarkedString.unapply)
        case _ => MarkedString.unapply(json).map(List(_))
      }
  }


  /* diagnostic messages */

  object MessageType {
    val Error = 1
    val Warning = 2
    val Info = 3
    val Log = 4
  }

  object ShowMessage extends Notification("window/showMessage") {
    def apply(message_type: Int, message: String): JSON.T =
      Notification(name, JSON.Object("type" -> message_type, "message" -> message))
  }

  object LogMessage extends Notification("window/logMessage") {
    def apply(message_type: Int, message: String): JSON.T =
      Notification(name, JSON.Object("type" -> message_type, "message" -> message))
  }


  /* commands */

  sealed case class Command(title: String, command: String, arguments: List[JSON.T] = Nil) {
    def json: JSON.T =
      JSON.Object("title" -> title, "command" -> command, "arguments" -> arguments)
  }


  /* document edits */

  object DidOpenTextDocument extends Notification("textDocument/didOpen") {
    def unapply(json: JSON.T): Option[(String, String, Long, String)] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            doc <- JSON.value(params, "textDocument")
            uri <- JSON.string(doc, "uri") if Url.is_wellformed_file(uri)
            lang <- JSON.string(doc, "languageId")
            version <- JSON.long(doc, "version")
            text <- JSON.string(doc, "text")
          } yield (uri, lang, version, text)
        case _ => None
      }
  }


  sealed case class TextDocumentChange(range: Option[Line.Range], text: String)

  object DidChangeTextDocument extends Notification("textDocument/didChange") {
    def unapply_change(json: JSON.T): Option[TextDocumentChange] =
      for (text <- JSON.string(json, "text"))
      yield TextDocumentChange(JSON.value(json, "range", Range.unapply), text)

    def unapply(json: JSON.T): Option[(String, Long, List[TextDocumentChange])] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            doc <- JSON.value(params, "textDocument")
            uri <- JSON.string(doc, "uri") if Url.is_wellformed_file(uri)
            version <- JSON.long(doc, "version")
            changes <- JSON.list(params, "contentChanges", unapply_change)
          } yield (uri, version, changes)
        case _ => None
      }
  }

  class TextDocumentNotification(name: String) extends Notification(name) {
    def unapply(json: JSON.T): Option[String] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            doc <- JSON.value(params, "textDocument")
            uri <- JSON.string(doc, "uri") if Url.is_wellformed_file(uri)
          } yield uri
        case _ => None
      }
  }

  object DidCloseTextDocument extends TextDocumentNotification("textDocument/didClose")
  object DidSaveTextDocument extends TextDocumentNotification("textDocument/didSave")


  /* workspace edits */

  object TextEdit {
    def unapply(json: JSON.T): Option[TextEdit] =
      for {
        case Range(range) <- JSON.value(json, "range")
        new_text <- JSON.string(json, "newText")
      } yield TextEdit(range, new_text)
  }

  sealed case class TextEdit(range: Line.Range, new_text: String) {
    def json: JSON.T = JSON.Object("range" -> Range(range), "newText" -> new_text)
  }

  object Document_Edit extends Notification("PIDE/document_edit") {
    def unapply(json: JSON.T): Option[Document_Edit] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            uri <- JSON.string(params, "uri")
            case TextEdit(edit) <- JSON.value(params, "edit")
            pos <- Position.unapply(params)
          } yield Document_Edit(uri, JSON.long(params, "version"), edit, pos)
        case _ => None
      }
  }

  sealed case class Document_Edit(
    uri: String,
    version: Option[Long],
    edit: TextEdit,
    end_pos: Line.Position
  ) {
    def json: JSON.T =
      Notification(Document_Edit.name,
        JSON.Object(
          "uri" -> uri,
          "edit" -> edit.json,
          "line" -> end_pos.line,
          "character" -> end_pos.column) ++
        JSON.optional("version" -> version))
  }

  sealed case class TextDocumentEdit(uri: String, version: Option[Long], edits: List[TextEdit]) {
    def json: JSON.T =
      JSON.Object(
        "textDocument" -> (
          JSON.Object("uri" -> uri) ++
          JSON.optional("version" -> version)
        ),
        "edits" -> edits.map(_.json)
      )
  }

  object WorkspaceEdit {
    def apply(edits: List[TextDocumentEdit]): JSON.T =
      JSON.Object("documentChanges" -> edits.map(_.json))
  }

  object ApplyWorkspaceEdit extends Request("workspace/applyEdit") {
    def apply(edits: List[TextDocumentEdit]): JSON.T =
      RequestMessage(Id.empty, name, JSON.Object("edit" -> WorkspaceEdit(edits)))
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
      JSON.optional("textEdit" -> range.map(TextEdit(_, text.getOrElse(label)).json)) ++
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


  /* goto requests */

  object GotoDefinition extends RequestTextDocumentPosition("textDocument/definition") {
    def reply(id: Id, result: List[Line.Node_Range]): JSON.T =
      ResponseMessage(id, Some(result.map(Location.apply)))
  }

  object Goto_File extends Notification("PIDE/goto_file") {
    def apply(file_name: String): JSON.T = Notification(name, JSON.Object("name" -> file_name))

    def unapply(json: JSON.T): Option[String] =
      json match {
        case Notification(method, params) if method == name => JSON.string(params, "name")
        case _ => None
      }
  }

  object Goto_Source_File extends Notification("PIDE/goto_source_file") {
    def apply(file_name: String, line: Int, offset: Symbol.Offset): JSON.T =
      Notification(name, JSON.Object("name" -> file_name, "line" -> line, "offset" -> offset))

    def unapply(json: JSON.T): Option[(String, Int, Symbol.Offset)] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            name <- JSON.string(params, "name")
            line <- JSON.int(params, "line")
            offset <- JSON.int(params, "offset")
          } yield (name, line, offset)
        case _ => None
      }
  }

  object Goto_Command extends Notification("PIDE/goto_command") {
    def apply(id: Long, offset: Symbol.Offset): JSON.T =
      Notification(name, JSON.Object("id" -> id, "offset" -> offset))

    def unapply(json: JSON.T): Option[(Long, Symbol.Offset)] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            id <- JSON.long(params, "id")
            offset <- JSON.int(params, "offset")
          } yield (id, offset)
        case _ => None
      }
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

  object PublishDiagnostics extends Notification("textDocument/publishDiagnostics") {
    def apply(uri: String, diagnostics: List[Diagnostic]): JSON.T =
      Notification(name, JSON.Object("uri" -> uri, "diagnostics" -> diagnostics.map(_.json)))
  }


  /* actions */

  sealed case class CodeAction(title: String, edits: List[TextDocumentEdit]) {
    def json: JSON.T =
      JSON.Object("title" -> title, "edit" -> WorkspaceEdit(edits))
  }

  object CodeActionRequest extends Request("textDocument/codeAction") {
    def unapply(json: JSON.T): Option[(Id, String, Line.Range)] =
      json match {
        case RequestMessage(id, method, params) if method == name =>
          for {
            doc <- JSON.value(params, "textDocument")
            uri <- JSON.string(doc, "uri") if Url.is_wellformed_file(uri)
            case Range(range) <- JSON.value(params, "range")
          } yield (id, uri, range)
        case _ => None
      }

    def reply(id: Id, actions: List[CodeAction]): JSON.T =
      ResponseMessage(id, Some(actions.map(_.json)))
  }

  object Markup_Action extends Notification("PIDE/markup_action") {
    def apply(active: XML.Elem, text: String): JSON.T =
      Notification(name, JSON.Object("active" -> YXML.string_of_tree(active), "text" -> text))

    def unapply(json: JSON.T): Option[(XML.Elem, String)] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            active <- JSON.string(params, "active")
            text <- JSON.string(params, "text")
            case XML.Elem(markup, body) <- Some(YXML.parse_elem(YXML.Source(active)))
          } yield (XML.Elem(markup, body), text)
        case _ => None
      }
  }


  /* decorations */

  object Decoration_Range {
    def unapply(json: JSON.T): Option[Decoration_Range] =
      for {
        coords <- JSON.list(json, "range", JSON.Value.Int.unapply)
        range <- Range.expand(coords)
      } yield {
        val msg = for (case MarkedStrings(strs) <- JSON.value(json, "hover_message")) yield strs
        Decoration_Range(range, msg.getOrElse(Nil))
      }
  }

  sealed case class Decoration_Range(range: Line.Range, hover_message: List[MarkedString] = Nil) {
    def json: JSON.T =
      JSON.Object("range" -> Range.compact(range)) ++
      JSON.optional("hover_message" -> MarkedStrings.json(hover_message))
  }

  object Decoration_Entry {
    def text_color(color: Rendering.Color.Value, content: List[Decoration_Range]): Decoration_Entry =
      Decoration_Entry("text_" + color.toString, content)

    def unapply(json: JSON.T): Option[Decoration_Entry] =
      for {
        typ <- JSON.string(json, "type")
        content <- JSON.list(json, "content", Decoration_Range.unapply)
      } yield Decoration_Entry(typ, content)
  }

  sealed case class Decoration_Entry(typ: String, content: List[Decoration_Range]) {
    def json: JSON.T = JSON.Object("type" -> typ, "content" -> content.map(_.json))
  }

  object Decoration_Entries {
    def unapply(json: JSON.T): Option[Decoration_Entries] =
      JSON.Value.List.unapply(json, Decoration_Entry.unapply).map(Decoration_Entries(_))
  }

  sealed case class Decoration_Entries(entries: List[Decoration_Entry]) {
    def json_entries: JSON.T = entries.map(_.json)
  }

  object Decoration extends Notification("PIDE/decoration") {
    def unapply(json: JSON.T): Option[Decoration] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            uri <- JSON.string(params, "uri")
            entries <- JSON.list(params, "entries", Decoration_Entry.unapply)
          } yield Decoration(uri, entries)
        case _ => None
      }
  }

  sealed case class Decoration(uri: String, entries: List[Decoration_Entry]) {
    def json: JSON.T =
      Notification(Decoration.name, JSON.Object("uri" -> uri, "entries" -> entries.map(_.json)))
  }

  object Decoration_Request extends Notification("PIDE/decoration_request") {
    def unapply(json: JSON.T): Option[String] =
      json match {
        case Notification(method, params) if method == name =>
          for (uri <- JSON.string(params, "uri") if Url.is_wellformed_file(uri)) yield uri
        case _ => None
      }
  }


  /* caret update: bidirectional */

  object Caret_Update extends Notification("PIDE/caret_update") {
    def apply(node_pos: Line.Node_Position, focus: Boolean): Caret_Update =
      Caret_Update(Url.print_file_name(node_pos.name), node_pos.pos, focus = focus)

    def unapply(json: JSON.T): Option[Option[Caret_Update]] =
      json match {
        case Notification(method, params) if method == name =>
          val caret =
            for {
              uri <- JSON.string(params, "uri")
              pos <- Position.unapply(params)
              focus <- JSON.bool(params, "focus")
            } yield Caret_Update(uri, pos, focus)
          Some(caret)
        case _ => None
      }
  }

  sealed case class Caret_Update(uri: String, pos: Line.Position, focus: Boolean = false) {
    def json: JSON.T =
      Notification(Caret_Update.name,
        JSON.Object(
          "uri" -> uri,
          "line" -> pos.line,
          "character" -> pos.column,
          "focus" -> focus))
  }


  /* dynamic output */

  object Dynamic_Output extends Notification("PIDE/dynamic_output") {
    def apply(content: String, decorations: Option[Decoration_Entries] = None): JSON.T =
      Notification(name,
        JSON.Object("content" -> content) ++
        JSON.optional("decorations" -> decorations.map(_.json_entries)))

    def unapply(json: JSON.T): Option[(String, Option[Decoration_Entries])] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            content <- JSON.string(params, "content")
            decorations = JSON.value(params, "decorations", Decoration_Entries.unapply)
          } yield (content, decorations)
        case _ => None
      }
  }

  object Output_Set_Margin extends Notification("PIDE/output_set_margin") {
    def unapply(json: JSON.T): Option[Double] =
      json match {
        case Notification(method, params) if method == name =>
          JSON.double(params, "margin")
        case _ => None
      }
  }


  /* state output */

  object State_Output extends Notification("PIDE/state_output") {
    def unapply(json: JSON.T): Option[State_Output] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            id <- JSON.long(params, "id")
            content <- JSON.string(params, "content")
            auto_update <- JSON.bool(params, "auto_update")
            decorations = JSON.value(params, "decorations", Decoration_Entries.unapply)
          } yield State_Output(id, content, auto_update, decorations)
        case _ => None
      }
  }

  case class State_Output(
    id: Counter.ID,
    content: String,
    auto_update: Boolean,
    decorations: Option[Decoration_Entries]
  ) {
    def json: JSON.T =
      Notification(State_Output.name,
        JSON.Object("id" -> id, "content" -> content, "auto_update" -> auto_update) ++
        JSON.optional("decorations" -> decorations.map(_.json_entries)))
  }

  class State_Id_Notification(name: String) extends Notification(name) {
    def apply(id: Counter.ID): JSON.T = Notification(name, JSON.Object("id" -> id))

    def unapply(json: JSON.T): Option[Counter.ID] =
      json match {
        case Notification(method, params) if method == name => JSON.long(params, "id")
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

  object State_Auto_Update extends Notification("PIDE/state_auto_update") {
    def apply(id: Counter.ID, enabled: Boolean): JSON.T =
      Notification(name, JSON.Object("id" -> id, "enabled" -> enabled))

    def unapply(json: JSON.T): Option[(Counter.ID, Boolean)] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            id <- JSON.long(params, "id")
            enabled <- JSON.bool(params, "enabled")
          } yield (id, enabled)
        case _ => None
      }
  }

  object State_Set_Margin extends Notification("PIDE/state_set_margin") {
    def unapply(json: JSON.T): Option[(Counter.ID, Double)] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            id <- JSON.long(params, "id")
            margin <- JSON.double(params, "margin")
          } yield (id, margin)
        case _ => None
      }
  }


  /* preview */

  object Preview_Request extends Notification("PIDE/preview_request") {
    def apply(uri: String, column: Int): JSON.T =
      Notification(name, JSON.Object("uri" -> uri, "column" -> column))

    def unapply(json: JSON.T): Option[(String, Int)] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            uri <- JSON.string(params, "uri") if Url.is_wellformed_file(uri)
            column <- JSON.int(params, "column")
          } yield (uri, column)
        case _ => None
      }
  }

  object Preview_Response extends Notification("PIDE/preview_response") {
    def apply(uri: String, column: Int, label: String, content: String): JSON.T =
      Notification(name,
        JSON.Object(
          "uri" -> uri,
          "column" -> column,
          "label" -> label,
          "content" -> content))

    def unapply(json: JSON.T): Option[(String, Int, String, String)] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            uri <- JSON.string(params, "uri")
            column <- JSON.int(params, "column")
            label <- JSON.string(params, "label")
            content <- JSON.string(params, "content")
          } yield (uri, column, label, content)
        case _ => None
      }
  }


  /* abbrevs */

  object Abbrevs_Request extends Notification0("PIDE/abbrevs_request")

  object Abbrevs_Response extends Notification("PIDE/abbrevs_response") {
    def apply(abbrevs: List[(String, String)]): JSON.T =
      Notification(name, JSON.Object("abbrevs" -> (for ((a, b) <- abbrevs) yield List(a, b))))

    def unapply(json: JSON.T): Option[List[(String, String)]] =
      json match {
        case Notification(method, params) if method == name =>
          JSON.list(params, "abbrevs",
            { case List(a: String, b: String) => Some(a, b) case _ => None })
        case _ => None
      }
  }


  /* documentation */

  object Documentation_Request
    extends Notification0("PIDE/documentation_request")

  object Doc_Entry {
    def apply(entry: Doc.Entry): JSON.T =
      JSON.Object(
        "name" -> entry.name,
        "path" -> entry.path.implode,
        "title" -> entry.title)

    def unapply(json: JSON.T): Option[Doc.Entry] =
      for {
        name <- JSON.string(json, "name")
        path <- JSON.string(json, "path")
        title <- JSON.string(json, "title")
      } yield Doc.Entry(name, Path.explode(path), title)
  }

  object Doc_Section {
    def apply(section: Doc.Section): JSON.T =
      JSON.Object(
        "title" -> section.title,
        "important" -> section.important,
        "entries" -> section.entries.map(Doc_Entry.apply))

    def unapply(json: JSON.T): Option[Doc.Section] =
      for {
        title <- JSON.string(json, "title")
        important <- JSON.bool(json, "important")
        entries <- JSON.list(json, "entries", Doc_Entry.unapply)
      } yield Doc.Section(title, important, entries)
  }

  object Documentation_Response extends Notification("PIDE/documentation_response") {
    def apply(doc_contents: Doc.Contents): JSON.T =
      Notification(name, JSON.Object("sections" -> doc_contents.sections.map(Doc_Section.apply)))

    def unapply(json: JSON.T): Option[Doc.Contents] =
      json match {
        case Notification(method, params) if method == name =>
          for (contents <- JSON.list(params, "sections", Doc_Section.unapply))
          yield Doc.Contents(contents)
        case _ => None
      }
  }


  /* sledgehammer */

  object Sledgehammer_Provers_Request
    extends Notification0("PIDE/sledgehammer_provers_request")

  object Sledgehammer_Provers_Response extends Notification("PIDE/sledgehammer_provers_response") {
    def apply(provers: String): JSON.T = Notification(name, JSON.Object("provers" -> provers))

    def unapply(json: JSON.T): Option[String] =
      json match {
        case Notification(method, params) if method == name => JSON.string(params, "provers")
        case _ => None
      }
  }

  object Sledgehammer_Request extends Notification("PIDE/sledgehammer_request") {
    def apply(provers: String, isar: Boolean, try0: Boolean): JSON.T =
      Notification(name, JSON.Object("provers" -> provers, "isar" -> isar, "try0" -> try0))

    def unapply(json: JSON.T): Option[List[String]] =
      json match {
        case Notification(method, params) if method == name =>
          for {
            provers <- JSON.string(params, "provers")
            isar <- JSON.bool(params, "isar")
            try0 <- JSON.bool(params, "try0")
          } yield List(provers, isar.toString, try0.toString)
        case _ => None
      }
  }

  object Sledgehammer_Status extends Notification("PIDE/sledgehammer_status") {
    def apply(message: String): JSON.T = Notification(name, JSON.Object("message" -> message))

    def unapply(json: JSON.T): Option[String] =
      json match {
        case Notification(method, params) if method == name => JSON.string(params, "message")
        case _ => None
      }
  }

  object Sledgehammer_Output extends Notification("PIDE/sledgehammer_output") {
    def apply(content: String): JSON.T = Notification(name, JSON.Object("content" -> content))

    def unapply(json: JSON.T): Option[String] =
      json match {
        case Notification(method, params) if method == name => JSON.string(params, "content")
        case _ => None
      }
  }

  object Sledgehammer_Cancel extends Notification0("PIDE/sledgehammer_cancel")

  object Sledgehammer_Locate extends Notification0("PIDE/sledgehammer_locate")
}
