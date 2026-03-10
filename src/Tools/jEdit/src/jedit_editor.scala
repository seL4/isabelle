/*  Title:      Tools/jEdit/src/jedit_editor.scala
    Author:     Makarius

PIDE editor operations for jEdit.
*/

package isabelle.jedit


import isabelle._


import org.gjt.sp.jedit.{View, Buffer}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.browser.VFSBrowser
import org.gjt.sp.jedit.textarea.{TextArea, TextAreaPainter, JEditTextArea}
import org.gjt.sp.util.AwtRunnableQueue


object JEdit_Editor extends Editor {
  /** context **/

  object Context {
    def apply(view: View): Dynamic_Context = new Dynamic_Context(view)
    def apply(view: View, text_area: TextArea): Static_Context = new Static_Context(view, text_area)
    def apply(text_area: JEditTextArea): Static_Context = apply(text_area.getView, text_area)
  }

  trait Context {
    /* view */

    def view: View


    /* text area (NB: JEditTextArea <: TextArea) */

    def text_area: TextArea

    def text_area_painter: TextAreaPainter =
      if (text_area == null) null else text_area.getPainter

    def proper_text_area: Option[JEditTextArea] =
      text_area match {
        case jedit_text_area: JEditTextArea => Some(jedit_text_area)
        case _ => None
      }

    def caret_offset: Text.Offset =
      if (text_area == null) 0 else text_area.getCaretPosition

    def caret_range: Text.Range =
      JEdit_Lib.point_range(buffer, caret_offset)


    /* buffer (NB: Buffer <: JEditBuffer) */

    def buffer: JEditBuffer =
      if (text_area == null) null else text_area.getBuffer

    def buffer_name: String = JEdit_Lib.buffer_name(buffer)

    def buffer_range: Text.Range =
      if (buffer == null) Text.Range.offside else JEdit_Lib.buffer_range(buffer)

    def proper_buffer: Option[Buffer] =
      buffer match {
        case buf: Buffer => Some(buf)
        case _ => None
      }
  }

  // view with dynamic text_area/buffer
  class Dynamic_Context private[JEdit_Editor](override val view: View) extends Context {
    override def text_area: TextArea = view.getTextArea
  }

  // view with static text area/buffer
  class Static_Context private[JEdit_Editor](
    override val view: View, override val text_area: TextArea) extends Context



  /** PIDE session and document model **/

  type Session = JEdit_Session

  override def session: Session = PIDE.session

  def flush_edits(hidden: Boolean = false, purge: Boolean = false): Unit =
    GUI_Thread.require {
      val (doc_blobs, edits) = Document_Model.flush_edits(hidden, purge)
      session.update(doc_blobs, edits)
    }
  override def flush(): Unit = flush_edits()
  def purge(): Unit = flush_edits(purge = true)

  private val delay_input: Delay =
    Delay.last(PIDE.session.input_delay, gui = true) { flush() }

  private val delay_generated_input: Delay =
    Delay.first(PIDE.session.generated_input_delay, gui = true) { flush() }

  def invoke(): Unit = delay_input.invoke()
  def revoke(): Unit = delay_input.revoke()
  def invoke_generated(): Unit = { delay_input.invoke(); delay_generated_input.invoke() }

  def shutdown(): Unit =
    GUI_Thread.require {
      delay_input.revoke()
      delay_generated_input.revoke()
      Document_Model.flush_edits(hidden = false, purge = false)
    }

  def visible_node(name: Document.Node.Name): Boolean =
    (for {
      text_area <- JEdit_Lib.jedit_text_areas()
      doc_view <- Document_View.get(text_area)
    } yield doc_view.model.node_name).contains(name)


  override def get_models(): Iterable[Document.Model] = Document_Model.get_models()


  /* global changes */

  def state_changed(): Unit = {
    GUI_Thread.later { flush() }
    PIDE.session.deps_changed()
    session.global_options.post(Session.Global_Options(PIDE.options))
  }

  override def document_state_changed(): Unit = state_changed()


  /* current situation */

  override def current_node(editor_context: Context): Option[Document.Node.Name] =
    GUI_Thread.require { Document_Model.get_model(editor_context.buffer).map(_.node_name) }

  override def current_node_snapshot(editor_context: Context): Option[Document.Snapshot] =
    GUI_Thread.require { Document_Model.get_snapshot(editor_context.buffer) }

  override def node_snapshot(name: Document.Node.Name): Document.Snapshot =
    GUI_Thread.require { Document_Model.get_snapshot(name) getOrElse session.snapshot(name) }

  override def current_command(editor_context: Context, snapshot: Document.Snapshot): Option[Command] =
    GUI_Thread.require {
      val caret_offset = editor_context.caret_offset
      Document_View.get(editor_context.text_area) match {
        case Some(doc_view) if snapshot.loaded_theory_command(caret_offset).isEmpty =>
          snapshot.current_command(doc_view.model.node_name, caret_offset)
        case _ => None
      }
    }


  /* output messages */

  override def output_state(): Boolean = JEdit_Options.output_state()


  /* overlays */

  override def node_overlays(name: Document.Node.Name): Document.Node.Overlays =
    Document_Model.node_overlays(name)

  override def insert_overlay(command: Command, fn: String, args: List[String]): Unit =
    Document_Model.insert_overlay(command, fn, args)

  override def remove_overlay(command: Command, fn: String, args: List[String]): Unit =
    Document_Model.remove_overlay(command, fn, args)



  /** navigation **/

  def goto_file(
    editor_context: Context,
    name: String,
    line: Int = -1,
    offset: Text.Offset = -1,
    focus: Boolean = false
  ): Unit = {
    GUI_Thread.require {}

    val view = editor_context.view
    val navigator = Isabelle_Navigator.get(view)
    val target = Isabelle_Navigator.Target(line = line, offset = offset)

    JEdit_Lib.jedit_buffer(name) match {
      case Some(buffer) => navigator.goto_buffer(buffer, target, focus = focus)
      case None if JEdit_Lib.is_virtual_dir(view, name) => VFSBrowser.browseDirectory(view, name)
      case None =>
        if (!Isabelle_System.open_external_file(name)) navigator.open_file(name, target)
    }
  }

  def goto_doc(editor_context: Context, path: Path, focus: Boolean = false): Unit = {
    if (path.is_pdf) Doc.view(path)
    else goto_file(editor_context, File.platform_path(path), focus = focus)
  }


  /* hyperlinks */

  def hyperlink_doc(name: String): Option[Hyperlink] =
    session.doc_entry(name).map(entry =>
      new Hyperlink {
        override val external: Boolean = !entry.path.is_file
        def follow(editor_context: Context): Unit =
          goto_doc(editor_context, entry.path, focus = true)
        override def toString: String = "doc " + quote(name)
      })

  def hyperlink_url(name: String): Hyperlink =
    new Hyperlink {
      override val external = true
      def follow(editor_context: Context): Unit =
        Isabelle_Thread.fork(name = "hyperlink_url") {
          try { Isabelle_System.open(Url.escape_name(name)) }
          catch {
            case exn: Throwable =>
              val view = editor_context.view
              GUI_Thread.later {
                GUI.error_dialog(view, "System error", GUI.scrollable_text(Exn.message(exn)))
              }
          }
        }
      override def toString: String = "URL " + quote(name)
    }

  def hyperlink_file(
    name: String,
    line: Int = -1,
    offset: Text.Offset = -1,
    description: String = "",
    focus: Boolean = false
  ): Hyperlink =
    new Hyperlink {
      def follow(editor_context: Context): Unit =
        goto_file(editor_context, name, line = line, offset = offset, focus = focus)
      override def toString: String =
        proper_string(description).getOrElse("file " + quote(name))
    }

  def hyperlink_source_file(
    source_name: String,
    line1: Int,
    offset: Symbol.Offset,
    description: String = "",
    focus: Boolean = false,
  ) : Option[Hyperlink] = {
    for (platform_path <- PIDE.session.store.source_file(source_name)) yield {
      def hyperlink(pos: Line.Position) =
        hyperlink_file(platform_path, line = pos.line, offset = pos.column,
          description = description, focus = focus)

      if (offset > 0) {
        PIDE.resources.get_file_content(PIDE.resources.node_name(platform_path)) match {
          case Some(text) =>
            hyperlink(
              Symbol.iterator(text).zipWithIndex.takeWhile(p => p._2 < offset - 1).map(_._1).
                foldLeft(Line.Position.zero)(_.advance(_)))
          case None =>
            hyperlink(Line.Position((line1 - 1) max 0))
        }
      }
      else hyperlink(Line.Position((line1 - 1) max 0))
    }
  }

  override def hyperlink_command(
    snapshot: Document.Snapshot,
    id: Document_ID.Generic,
    offset: Symbol.Offset = 0,
    description: String = "",
    focus: Boolean = false
  ) : Option[Hyperlink] = {
    if (snapshot.is_outdated) None
    else {
      for (pos <- snapshot.find_command_position(id, offset)) yield
        hyperlink_file(pos.name, line = pos.line, offset = pos.column,
          description = description, focus = focus)
    }
  }

  def is_hyperlink_position(
    snapshot: Document.Snapshot,
    text_offset: Text.Offset,
    pos: Position.T
  ): Boolean = {
    (for {
      (id, range) <- Position.Item_Id.unapply(pos) if range.start > 0
      command <- snapshot.get_command(id)
      start <- snapshot.command_start(command)
    } yield text_offset == start + command.chunk.decode(range.start)) getOrElse false
  }

  def hyperlink_position(
    snapshot: Document.Snapshot,
    pos: Position.T,
    description: String = "",
    focus: Boolean = false
  ): Option[Hyperlink] = {
    pos match {
      case Position.Item_File(name, line, range) =>
        hyperlink_source_file(name, line, range.start, description = description, focus = focus)
      case Position.Item_Id(id, range) =>
        hyperlink_command(snapshot, id, range.start, description = description, focus = focus)
      case _ => None
    }
  }

  def hyperlink_def_position(
    snapshot: Document.Snapshot,
    pos: Position.T,
    description: String = "",
    focus: Boolean = false
  ): Option[Hyperlink] = {
    pos match {
      case Position.Item_Def_File(name, line, range) =>
        hyperlink_source_file(name, line, range.start, description = description, focus = focus)
      case Position.Item_Def_Id(id, range) =>
        hyperlink_command(snapshot, id, range.start, description = description, focus = focus)
      case _ => None
    }
  }


  /* navigator */

  override def navigator_record(editor_context: Context): Boolean =
    Isabelle_Navigator.get(editor_context.view).record(Isabelle_Navigator.Pos(editor_context))

  override def navigator_recording[A](editor_context: Context)(body: => A): A = {
    navigator_record(editor_context)
    val res = body
    navigator_record(editor_context)
    res
  }



  /** GUI dispatcher thread **/

  override def assert_dispatcher[A](body: => A): A = GUI_Thread.assert(body)
  override def require_dispatcher[A](body: => A): A = GUI_Thread.require(body)
  override def send_dispatcher(body: => Unit): Unit = GUI_Thread.later(body)
  override def send_wait_dispatcher(body: => Unit): Unit = GUI_Thread.now(body)
}
