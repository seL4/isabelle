/*  Title:      Tools/VSCode/extension/src/vscode.scala
    Author:     Fabian Huch

VSCode APIs in Isabelle/Scala.
*/

package isabelle.vscode.extension

import scala.scalajs.js
import scala.scalajs.js.JSConverters._

import isabelle._
import isabelle.vscode._


object VSCode {
  abstract class JS_Ref(private val rep: js.Any) {
    override def hashCode: Int = rep.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: JS_Ref => other.rep == rep
        case _ => false
      }
  }


  /* basic types */

  trait Disposable extends js.Object { def dispose(): Unit }

  object Future {
    private[VSCode] def apply[A](rep: js.Thenable[A]): Future[A] = new Future(rep)
  }

  class Future[A] private(private[VSCode] val rep: js.Thenable[A]) extends JS_Ref(rep) {
    def map[B](f: A => B): Future[B] = Future[B](rep.`then`(a => f(a), js.undefined))
    def flatMap[B](f: A => Future[B]): Future[B] =
      Future[B](rep.`then`(value => f(value).rep, js.undefined))
  }


  /* position and range */

  @js.native
  @js.annotation.JSImport("vscode", "Position")
  private class Position(val line: Int, val character: Int) extends js.Object

  private object Position {
    def apply(p: Line.Position): Position = new Position(p.line, p.column)
    def apply(p: Position): Line.Position = Line.Position(p.line, p.character)
  }

  @js.native
  @js.annotation.JSImport("vscode", "Range")
  private class Range(val start: Position, val end: Position) extends js.Object

  private object Range {
    def apply(r: Line.Range): Range = new Range(Position(r.start), Position(r.stop))
    def apply(r: Range): Line.Range = Line.Range(Position(r.start), Position(r.end))
  }


  /* events */

  private type Event_Fun[A] = js.Function1[js.Function1[A, Unit], Disposable]

  @js.native
  @js.annotation.JSImport("vscode", "EventEmitter")
  private class EventEmitter[A] extends js.Object {
    val event: Event_Fun[A] = js.native
    def fire(data: A): Unit = js.native
    def dispose(): Unit = js.native
  }

  object Event {
    class Emitter[A] extends Disposable {
      private val rep = new EventEmitter[A]

      val event: Event[A] = Event(rep.event)
      def fire(data: A): Unit = rep.fire(data)
      def dispose(): Unit = rep.dispose()
    }

    private[VSCode] def apply[A](e: Event_Fun[A]): VSCode.Event[A] = apply(e, (value: A) => value)
    private[VSCode] def apply[A, B](e: Event_Fun[A], convert: A => B): VSCode.Event[B] =
      (listener: B => Unit) => e((value: A) => listener(convert(value)))
  }

  trait Event[+A] { def apply(listener: A => Unit): Disposable }


  /* URIs (RFC 3986) */

  @js.native
  @js.annotation.JSImport("vscode", "Uri")
  private object JS_Uri extends js.Object {
    def parse(value: String): JS_Uri = js.native
    def file(path: String): JS_Uri = js.native
  }

  @js.native
  @js.annotation.JSImport("vscode", "Uri")
  private class JS_Uri extends js.Object {
    override def toString(): String = js.native
    def scheme: String = js.native
    def path: String = js.native
    def fsPath: String = js.native
    def `with`(change: js.Object): JS_Uri = js.native
  }

  object Uri {
    private[VSCode] def apply(uri: JS_Uri): VSCode.Uri = new VSCode.Uri(uri)

    def parse(s: String): Uri = Uri(JS_Uri.parse(s))
    def file(platform_path: String): Uri = Uri(JS_Uri.file(platform_path))
    def file(path: Path): Uri = file(File.platform_path(path))
  }

  class Uri private(private[VSCode] val rep: JS_Uri) {
    override def toString: String = rep.toString
    override def hashCode: Int = rep.toString.hashCode
    override def equals(other: Any): Boolean =
      other match {
        case that: Uri => toString == that.toString
        case _ => false
      }

    def scheme: String = rep.scheme
    def path: String = rep.path
    def platform_path: String = rep.fsPath

    def is_file: Boolean = scheme == "file"

    def copy(scheme: String = this.scheme, path: String = this.path): Uri =
      Uri(rep.`with`(Scalajs.JSON.Object(JSON.Object("scheme" -> scheme, "path" -> path))))
  }


  /* documents */

  @js.native
  private trait TextDocument extends js.Object {
    val uri: JS_Uri = js.native
    def version: Int = js.native
    def getText(range: js.UndefOr[Range] = js.undefined): String = js.native
    def positionAt(offset: Int): Position = js.native
  }

  @js.native
  private trait TextDocumentChangeEvent extends js.Object {
    val document: TextDocument = js.native
  }

  object Document {
    private[VSCode] def apply(document: TextDocument): Document = new Document(document)

    case class Change(document: Document)
    private[VSCode] def change(e: TextDocumentChangeEvent): Change = Change(Document(e.document))
  }

  class Document private[VSCode](private[VSCode] val rep: TextDocument) {
    def uri: Uri = Uri(rep.uri)
    def version: Long = rep.version.toLong
    def text: String = rep.getText()
    def text(range: Line.Range): String = rep.getText(Range(range))
    def position(offset: Int): Line.Position = Position(rep.positionAt(offset))

    override def hashCode: Int = uri.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Document => uri == other.uri
        case _ => false
      }
  }


  /* decorations */

  @js.native
  @js.annotation.JSImport("vscode", "OverviewRulerLane")
  private object OverviewRulerLane extends js.Object {
    val Left: Int = js.native
    val Center: Int = js.native
    val Right: Int = js.native
    val Full: Int = js.native
  }

  @js.native
  @js.annotation.JSImport("vscode", "DecorationRangeBehavior")
  private object DecorationRangeBehavior extends js.Object {
    val OpenOpen: Int = js.native
    val ClosedClosed: Int = js.native
    val OpenClosed: Int = js.native
    val ClosedOpen: Int = js.native
  }

  object Decoration {
    case class Options(range: Line.Range, hover: List[LSP.MarkedString] = Nil) {
      def json: JSON.T =
        JSON.Object("range" -> LSP.Range(range), "hoverMessage" -> hover.map(_.json))
    }

    case class Themed(
      background_color: String = "",
      color: String = "",
      border: String = "",
      overview_ruler_color: String = ""
    ) {
      def json: JSON.Object.T =
        JSON.optional("backgroundColor" -> proper_string(background_color)) ++
        JSON.optional("color" -> proper_string(color)) ++
        JSON.optional("border" -> proper_string(border)) ++
        JSON.optional("overviewRulerColor" -> proper_string(overview_ruler_color))
    }

    enum Overview_Ruler_Lane { case left, center, right, full }
    enum Range_Behavior { case open_open, closed_closed, open_closed, closed_open }

    case class Rendering(
      text_decoration: String = "",
      light: Themed = Themed(),
      dark: Themed = Themed(),
      overview_ruler_lane: Overview_Ruler_Lane = Overview_Ruler_Lane.center,
      range_behavior: Range_Behavior = Range_Behavior.open_open
    ) {
      def json: JSON.Object.T =
        JSON.Object(
          "light" -> light.json,
          "dark" -> dark.json,
          "overviewRulerLane" -> 
            (overview_ruler_lane match {
              case Overview_Ruler_Lane.left => OverviewRulerLane.Left
              case Overview_Ruler_Lane.center => OverviewRulerLane.Center
              case Overview_Ruler_Lane.right => OverviewRulerLane.Right
              case Overview_Ruler_Lane.full => OverviewRulerLane.Full
            }),
          "rangeBehavior" ->
            (range_behavior match {
              case Range_Behavior.open_open => DecorationRangeBehavior.OpenOpen
              case Range_Behavior.closed_closed => DecorationRangeBehavior.ClosedClosed
              case Range_Behavior.open_closed => DecorationRangeBehavior.OpenClosed
              case Range_Behavior.closed_open => DecorationRangeBehavior.ClosedOpen
            })) ++
        JSON.optional("textDecoration" -> proper_string(text_decoration))
    }
  }

  trait Decoration extends Disposable


  /* text editor */

  @js.native
  @js.annotation.JSImport("vscode", "TextEditorRevealType")
  private object TextEditorRevealType extends js.Object {
    val Default: Int = js.native
    val InCenter: Int = js.native
    val InCenterIfOutsideViewport: Int = js.native
    val AtTop: Int = js.native
  }


  @js.native
  private trait Selection extends js.Object {
    val anchor: Position = js.native
    val active: Position = js.native
  }

  @js.native
  @js.annotation.JSImport("vscode", "ViewColumn")
  private object ViewColumn extends js.Object {
    val One: Int = js.native
    val Two: Int = js.native
    val Three: Int = js.native
  }

  @js.native
  private trait TextEditorEdit extends js.Object {
    def replace(location: Range, value: String): Unit = js.native
  }

  @js.native
  private trait TextEditor extends js.Object {
    val document: TextDocument = js.native
    val selection: Selection = js.native
    val viewColumn: js.UndefOr[Int] = js.native
    val visibleRanges: js.Array[Range] = js.native

    def edit(callback: js.Function1[TextEditorEdit, Unit]): js.Thenable[Boolean] = js.native
    def revealRange(range: Range, revealType: Int): Unit = js.native
    def setDecorations(decoration: Decoration, rangesOrOptions: js.Any): Unit =
      js.native
  }

  @js.native
  private trait TextEditorSelectionChangeEvent extends js.Object {
    val textEditor: TextEditor = js.native
  }

  @js.native
  private trait TextEditorVisibleRangesChangeEvent extends js.Object {
    val textEditor: TextEditor = js.native
  }

  object Text_Editor {
    case class Selection(anchor: Line.Position, active: Line.Position) {
      def is_empty: Boolean = anchor == active
      def is_reversed: Boolean = anchor.compare(active) > 0

      def start: Line.Position = if (is_reversed) active else anchor
      def end: Line.Position = if (is_reversed) anchor else active

      def range: Line.Range = Line.Range(start, end)
    }

    private[VSCode] def selection(s: VSCode.Selection): Selection =
      Selection(Position(s.anchor), Position(s.active))

    object Column {
      def one: Column = Column(ViewColumn.One)
      def two: Column = Column(ViewColumn.Two)
      def three: Column = Column(ViewColumn.Three)
    }

    case class Column(rep: Int)

    case class Show_Options(
      column: Option[Column] = None,
      preserve_focus: Boolean = false,
      selection: Option[Line.Range] = None
    ) {
      def json: JSON.Object.T =
        JSON.optional("viewColumn" -> column.map(_.rep)) ++
        JSON.Object("preserveFocus" -> preserve_focus) ++
        JSON.optional("selection" -> selection.map(LSP.Range(_)))
    }

    private[VSCode] def apply(rep: TextEditor): Text_Editor = new Text_Editor(rep)
  }

  class Text_Editor private(private val rep: TextEditor) extends JS_Ref(rep) {
    def document: Document = Document(rep.document)
    def selection: Text_Editor.Selection = Text_Editor.selection(rep.selection)
    def column: Option[Text_Editor.Column] = rep.viewColumn.toOption.map(Text_Editor.Column(_))
    def visible: List[Line.Range] = rep.visibleRanges.map(Range(_)).toList

    def reveal(range: Line.Range): Unit =
      rep.revealRange(Range(range), TextEditorRevealType.InCenterIfOutsideViewport)

    def edit(edits: List[LSP.TextEdit]): Future[Boolean] =
      Future(rep.edit((editor: TextEditorEdit) =>
        edits.foreach(edit => editor.replace(Range(edit.range), edit.new_text))))

    def set_decorations(decoration: Decoration, options: List[Decoration.Options] = Nil): Unit =
      rep.setDecorations(decoration, Scalajs.JSON(options.map(_.json)))
  }


  /* webviews */

  @js.native
  private trait JS_Webview extends js.Object {
    var html: String = js.native
    var options: js.Object = js.native
    val onDidReceiveMessage: Event_Fun[js.Any] = js.native
    def postMessage(message: js.Any): js.Thenable[Boolean] = js.native
    def asWebviewUri(localResource: JS_Uri): JS_Uri = js.native
  }

  @js.native
  private trait WebviewView extends js.Object {
    val webview: JS_Webview = js.native
    val onDidDispose: Event_Fun[Unit] = js.native
  }

  private class WebviewViewProvider(provider: Webview.Provider) extends js.Object {
    def resolveWebviewView(webviewView: WebviewView, context: js.Object, token: js.Object): Unit = {
      webviewView.webview.options =
        js.Dynamic.literal(
          "enableScripts" -> true,
          "localResourceRoots" -> List(provider.context.uri.rep).toJSArray)
      val view = new Webview.View(webviewView)
      provider.resolve(view)
    }
  }

  @js.native
  private trait WebviewPanel extends js.Object {
    val webview: JS_Webview = js.native
    var title: String = js.native
    val onDidDispose: Event_Fun[Unit] = js.native
    def reveal(viewColumn: Int): Unit = js.native
    def dispose(): Unit = js.native
  }

  object Webview {
    final class View private[VSCode](private val rep: WebviewView) extends JS_Ref(rep) {
      def webview: Webview = new Webview(rep.webview)
      val on_dispose: Event[Unit] = Event(rep.onDidDispose, identity)
    }

    abstract class Provider(val name: String, val context: Extension.Context) {
      def resolve(view: View): Unit
    }

    private[VSCode] def provider(provider: Provider): WebviewViewProvider =
      new WebviewViewProvider(provider)

    final class Panel private[VSCode] (private val rep: WebviewPanel) extends Disposable {
      def webview: Webview = Webview(rep.webview)

      def title: String = rep.title
      def title_=(value: String): Unit = { rep.title = value }

      def reveal(column: Text_Editor.Column): Unit = rep.reveal(column.rep)

      def dispose(): Unit = rep.dispose()
      val on_dispose: Event[Unit] = Event.apply(rep.onDidDispose, identity)
    }
  }

  class Webview private(private val rep: JS_Webview) extends JS_Ref(rep) {
    def html: String = rep.html
    def html_=(value: String): Unit = { rep.html = value }

    def web_uri(local: Uri): Uri = Uri(rep.asWebviewUri(local.rep))

    def post_message(message: JSON.T): Future[Boolean] =
      Future(rep.postMessage(Scalajs.JSON(message)))

    val on_message: Event[JSON.T] = Event(rep.onDidReceiveMessage, Scalajs.JSON.unapply(_).get)
  }


  /* window */

  @js.native
  @js.annotation.JSImport("vscode", "ProgressLocation")
  private object ProgressLocation extends js.Object { val Notification: Int = js.native }

  @js.native
  private trait Progress[A] extends js.Object { def report(value: A): Unit = js.native }

  @js.native
  @js.annotation.JSImport("vscode", "window")
  private object JS_window extends js.Object {
    val activeTextEditor: js.UndefOr[TextEditor] = js.native
    val visibleTextEditors: js.Array[TextEditor] = js.native
    val onDidChangeActiveTextEditor: Event_Fun[js.UndefOr[TextEditor]] = js.native
    val onDidChangeVisibleTextEditors: Event_Fun[js.Array[TextEditor]] = js.native
    val onDidChangeTextEditorSelection: Event_Fun[TextEditorSelectionChangeEvent] = js.native
    val onDidChangeTextEditorVisibleRanges: Event_Fun[TextEditorVisibleRangesChangeEvent] =
      js.native
    def createTextEditorDecorationType(options: js.Any): Decoration = js.native
    def createWebviewPanel(viewType: String, title: String, showOptions: Int, options: js.Object)
      : WebviewPanel = js.native
    def registerWebviewViewProvider(viewId: String, provider: js.Object): Disposable = js.native
    def createTreeView(viewId: String, options: js.Object): Disposable = js.native
    def showTextDocument(document: TextDocument, options: js.Any): js.Thenable[TextEditor] =
      js.native
    def showErrorMessage(message: String): js.Thenable[js.UndefOr[String]] = js.native
    def withProgress[A](options: js.Any, task: js.Function1[Progress[js.Any], js.Thenable[A]])
     : js.Thenable[A] = js.native
  }

  object Window {
    def active_editor: Option[Text_Editor] = JS_window.activeTextEditor.toOption.map(Text_Editor(_))
    def visible_editors: List[Text_Editor] = JS_window.visibleTextEditors.toList.map(Text_Editor(_))

    val on_change_active_editor: Event[Option[Text_Editor]] =
      Event(JS_window.onDidChangeActiveTextEditor, _.toOption.map(Text_Editor(_)))

    val on_change_visible_editors: Event[List[Text_Editor]] =
      Event(JS_window.onDidChangeVisibleTextEditors, _.toList.map(Text_Editor(_)))

    val on_change_selection: Event[Text_Editor] =
      Event(JS_window.onDidChangeTextEditorSelection, e => Text_Editor(e.textEditor))

    val on_change_visible_ranges: Event[Text_Editor] =
      Event(JS_window.onDidChangeTextEditorVisibleRanges, e => Text_Editor(e.textEditor))

    def show_document(
      document: Document,
      options: Text_Editor.Show_Options = Text_Editor.Show_Options()
    ): Future[Text_Editor] =
      Future(
        JS_window.showTextDocument(document.rep, Scalajs.JSON(options.json))).map(Text_Editor(_))

    def show_error(message: String): Future[Unit] =
      Future(JS_window.showErrorMessage(message)).map(_ => {})

    class Progress private[Window](private val rep: VSCode.Progress[js.Any]) {
      def report(msg: String): Unit = rep.report(Scalajs.JSON(JSON.Object("message" -> msg)))
    }

    def with_progress[A](task: Progress => Future[A]): Future[A] =
      Future(
        JS_window.withProgress(
          Scalajs.JSON(JSON.Object("location" -> ProgressLocation.Notification)),
          (progress: VSCode.Progress[js.Any]) => task(new Progress(progress)).rep))

    def create_decoration(rendering: Decoration.Rendering): Decoration =
      JS_window.createTextEditorDecorationType(Scalajs.JSON(rendering.json))

    def register(provider: Webview.Provider): Disposable =
      JS_window.registerWebviewViewProvider(provider.name, Webview.provider(provider))

    def create_panel(name: String, title: String, column: Text_Editor.Column): Webview.Panel =
      new Webview.Panel(
        JS_window.createWebviewPanel(name, title, column.rep,
          js.Dynamic.literal("enableScripts" -> true)))

    def create_treeview[A](name: String, provider: Treeview.Provider[A]): Disposable =
      JS_window.createTreeView(name,
        js.Dynamic.literal("treeDataProvider" -> TreeDataProvider(provider)))
  }


  /* workspace */

  @js.native
  @js.annotation.JSImport("vscode", "FileType")
  private object FileType extends js.Object {
    val File: Int = js.native
    val SymbolicLink: Int = js.native
  }

  @js.native
  private trait FileStat extends js.Object {val `type`: Int = js.native }

  @js.native
  private trait FileSystem extends js.Object {
    def stat(uri: JS_Uri): js.Thenable[FileStat] = js.native
  }

  @js.native
  private trait WorkspaceConfiguration extends js.Object {
    def get[A](section: String): js.UndefOr[A] = js.native
    def update(section: String, value: js.Any): js.Thenable[Unit] = js.native
  }

  @js.native
  @js.annotation.JSImport("vscode", "WorkspaceEdit")
  private class WorkspaceEdit extends js.Object {
    def replace(uri: JS_Uri, range: Range, newText: String): Unit = js.native
  }

  @js.native
  @js.annotation.JSImport("vscode", "workspace")
  private object JS_workspace extends js.Object {
    val fs: FileSystem = js.native
    def getConfiguration(section: String): WorkspaceConfiguration = js.native
    def textDocuments: js.Array[TextDocument] = js.native
    def openTextDocument(uri: JS_Uri): js.Thenable[TextDocument] = js.native
    def applyEdit(edit: WorkspaceEdit): js.Thenable[Boolean] = js.native
    val onDidChangeConfiguration: Event_Fun[js.Any] = js.native
    val onDidChangeTextDocument: Event_Fun[TextDocumentChangeEvent] = js.native
    val onDidCloseTextDocument: Event_Fun[TextDocument] = js.native
  }

  object Workspace {
    def is_file(uri: Uri): Future[Boolean] =
      Future(JS_workspace.fs.stat(uri.rep).`then`[Boolean](stat =>
        stat.`type` == FileType.File || stat.`type` == (FileType.File | FileType.SymbolicLink),
        js.defined(_ => false)))

    def documents: List[Document] = JS_workspace.textDocuments.map(Document(_)).toList

    def open_document(uri: Uri): Future[Document] =
      Future(JS_workspace.openTextDocument(uri.rep)).map(Document(_))

    class Configuration private[Workspace](rep: WorkspaceConfiguration) extends JS_Ref(rep) {
      def get(section: String): Option[JSON.T] =
        rep.get[js.Any](section).toOption.map(Scalajs.JSON.unapply(_).get)

      def update(section: String, value: JSON.T): Unit = {
        rep.update(section, Scalajs.JSON(value))
      }

      def entries: JSON.Object.T =
        (for {
          key <- js.Object.keys(rep).toList
          value <- rep.get[js.Any](key).toList
          if js.typeOf(value) != "function"
        } yield key -> Scalajs.JSON.unapply(value).get).toMap
    }

    def configuration(section: String): Configuration =
      new Configuration(JS_workspace.getConfiguration(section))

    def edit(edit: LSP.TextDocumentEdit): Future[Boolean] = {
      val uri = Uri.parse(edit.uri)
      documents.find(_.uri == uri) match {
        case Some(doc) if edit.version.exists(_ != doc.version) => Future(js.Promise.resolve(false))
        case _ =>
          val rep = new WorkspaceEdit()
          edit.edits.foreach(e => rep.replace(uri.rep, Range(e.range), e.new_text))
          Future(JS_workspace.applyEdit(rep))
      }
    }

    val on_change_configuration: Event[Unit] = Event(JS_workspace.onDidChangeConfiguration, _ => {})

    val on_change_document: Event[Document.Change] =
      Event(JS_workspace.onDidChangeTextDocument, Document.change)

    val on_close_document: Event[Document] =
      Event(JS_workspace.onDidCloseTextDocument, Document(_))
  }


  /* language client */

  @js.native
  @js.annotation.JSImport("vscode-languageclient/node.js", "LanguageClient")
  private class LanguageClient(name: String, serverOptions: js.Any, clientOptions: js.Any)
    extends js.Object {

    def start(): Disposable = js.native
    def stop(): js.Promise[Unit] = js.native
    def onReady(): js.Promise[Unit] = js.native

    def sendNotification(method: String): Unit = js.native
    def sendNotification(method: String, params: js.Any): Unit = js.native
    def sendRequest[R](method: String): js.Promise[R] = js.native
    def sendRequest[R](method: String, param: js.Any): js.Promise[R] = js.native

    def onNotification(method: String, handler: js.Function): Disposable = js.native
  }

  object Language_Client {
    case class Server_Options(command: String, args: List[String]) {
      def json: JSON.Object.T = JSON.Object("command" -> command, "args" -> args)
    }

    case class Document_Filter(language: String = "", scheme: String = "") {
      require(language.nonEmpty || scheme.nonEmpty)

      def json: JSON.Object.T =
        JSON.optional("language" -> proper_string(language)) ++
          JSON.optional("scheme" -> proper_string(scheme))
    }

    case class Options(document_selector: List[Document_Filter]) {
      def json: JSON.Object.T = JSON.Object("documentSelector" -> document_selector.map(_.json))
    }

    def apply(name: String, server_options: Server_Options, options: Options): Language_Client =
      new Language_Client(
        new LanguageClient(name, Scalajs.JSON(server_options.json), Scalajs.JSON(options.json)))
  }

  class Language_Client private(rep: LanguageClient) {
    def start(): Disposable = rep.start()
    def stop(): Future[Unit] = Future(rep.stop())
    def on_ready(): Future[Unit] = Future(rep.onReady())

    def send_notification(json: JSON.T): Unit =
      json match {
        case LSP.Notification(method, params) => rep.sendNotification(method, Scalajs.JSON(params))
        case LSP.Notification0(method) => rep.sendNotification(method)
        case _ => error("Invalid LSP.Notification: " + JSON.Format(json))
      }

    def send_request(json: JSON.T): Future[JSON.T] =
      json match {
        case LSP.RequestMessage(_, method, params) =>
          Future(rep.sendRequest[js.Any](method, Scalajs.JSON(params))).map(
            Scalajs.JSON.unapply(_).get)
        case LSP.RequestMessage0(_, method) =>
          Future(rep.sendRequest[js.Any](method)).map(Scalajs.JSON.unapply(_).get)
      }

    def on_notification(method: String, handler: () => Unit): Disposable =
      rep.onNotification(method, handler)

    def on_notification(method: String, handler: PartialFunction[JSON.T, Unit]): Disposable =
      rep.onNotification(method, (params: js.Any) =>
        params match {
          case Scalajs.JSON(params) => handler(LSP.Notification(method, params))
          case _ =>
        })
  }


  /* extension */

  @js.native
  private trait ExtensionContext extends js.Object {
    val subscriptions: js.Array[Disposable] = js.native
    val extensionUri: JS_Uri = js.native
  }

  object Extension {
    type Ctxt = js.Object

    class Context private[Extension](private val rep: ExtensionContext) extends JS_Ref(rep) {
      def subscribe(s: Disposable*): Unit = rep.subscriptions.push(s: _*)
      def unsubscribe(s: Disposable): Unit = {
        val i = rep.subscriptions.indexOf(s)
        if (0 <= i) rep.subscriptions.remove(i)
      }
      def uri: Uri = Uri(rep.extensionUri)
    }

    def context(ctxt: Ctxt): Context = new Context(ctxt.asInstanceOf[ExtensionContext])
  }

  trait Extension {
    def activate(ctxt: Extension.Ctxt): Unit
    def deactivate(): Unit
  }


  /* commands */

  private trait Callback extends js.Function { def apply(args: Any*): Any }

  @js.native
  @js.annotation.JSImport("vscode", "commands")
  private object JS_commands extends js.Object {
    def registerCommand(command: String, callback: Callback): Disposable = js.native
    def executeCommand[A](command: String, rest: js.Any*): js.Thenable[A] = js.native
  }

  object Commands {
    private object Arg {
      def apply(a: Any): js.Any =
        a match {
          case () => js.undefined
          case l: Long => l.toDouble
          case p: Line.Position => Position(p)
          case r: Line.Range => Range(r)
          case u: Uri => u.rep
          case x => x.asInstanceOf[js.Any]
        }

      def unapply(a: Any): Option[Any] =
        Some(
          if (js.isUndefined(a)) ()
          else a match {
            case p: Position => Position(p)
            case r: Range => Range(r)
            case u: JS_Uri => Uri(u)
            case x => x
          })
    }

    def register(command: String, f: PartialFunction[Any, Any]): Disposable =
      JS_commands.registerCommand(command,
        (args: Seq[Any]) => {
          val arg =
            args.toList match {
              case Arg(arg) :: Nil => arg
              case _ => args.map(Arg.unapply(_).get).toJSArray
            }
          f.lift(arg).map {
            case t: Future[_] => t.map(Arg(_)).rep
            case r => Arg(r)
          }.orUndefined
        })

    def execute[A](command: String, rest: Any*): Future[A] =
      Future(JS_commands.executeCommand[Any](command, rest.map(Arg(_)): _*)).map {
        case Arg(value) => value.asInstanceOf[A]
      }

    case class Command(title: String, command: String, arguments: List[Any]) {
      private[VSCode] def rep: js.Object =
        js.Dynamic.literal(
          "title" -> title,
          "command" -> command,
          "arguments" -> arguments.map(Arg(_)).toJSArray)
    }
  }


  /* tree view */

  @js.native
  @js.annotation.JSImport("vscode", "TreeItemCollapsibleState")
  private object TreeItemCollapsibleState extends js.Object {
    val None: Int = js.native
    val Collapsed: Int = js.native
    val Expanded: Int = js.native
  }

  @js.native
  @js.annotation.JSImport("vscode", "TreeItem")
  private class TreeItem(label: String, collapsibleState: Int) extends js.Object {
    var id: js.UndefOr[String] = js.native
    var description: js.UndefOr[String] = js.native
    var tooltip: js.UndefOr[String] = js.native
    var resourceUri: js.UndefOr[JS_Uri] = js.native
    var command: js.UndefOr[js.Object] = js.native
  }

  private class TreeDataProvider[A](rep: Treeview.Provider[A]) extends js.Object {
    val onDidChangeTreeData: js.UndefOr[Event_Fun[js.UndefOr[js.Array[A]]]] =
      rep.on_change.map { event =>
        val f: Event_Fun[js.UndefOr[js.Array[A]]] =
        (listener: js.Function1[js.UndefOr[js.Array[A]], Unit]) =>
          event(elements => listener(if (elements.isEmpty) js.undefined else elements.toJSArray))
        f
      }.orUndefined

    def getTreeItem(element: A): TreeItem = rep.get_item(element).rep
    def getChildren(element: js.UndefOr[A]): js.Array[A] =
      rep.get_children(element.toOption).toJSArray
  }

  object Treeview {
    enum State { case none, collapsed, expanded }

    case class Item(
      label: String,
      state: State = State.none,
      id: String = "",
      description: String = "",
      tooltip: String = "",
      uri: Option[Uri] = None,
      command: Option[Commands.Command] = None
    ) {
      private[VSCode] def rep: TreeItem = {
        val js_state =
          state match {
            case State.none => TreeItemCollapsibleState.None
            case State.collapsed => TreeItemCollapsibleState.Collapsed
            case State.expanded => TreeItemCollapsibleState.Expanded
          }
        val item = new TreeItem(label, js_state)
        item.id = proper_string(id).orUndefined
        item.description = proper_string(description).orUndefined
        item.tooltip = proper_string(tooltip).orUndefined
        item.resourceUri = uri.map(_.rep).orUndefined
        item.command = command.map(_.rep).orUndefined
        item
      }
    }

    trait Provider[A] {
      def on_change: Option[Event[List[A]]] = None
      def get_children(element: Option[A]): List[A]
      def get_item(element: A): Item
    }
  }
}
