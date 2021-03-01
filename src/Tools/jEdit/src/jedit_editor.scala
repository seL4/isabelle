/*  Title:      Tools/jEdit/src/jedit_editor.scala
    Author:     Makarius

PIDE editor operations for jEdit.
*/

package isabelle.jedit


import isabelle._


import java.io.{File => JFile}

import org.gjt.sp.jedit.{jEdit, View, Buffer}
import org.gjt.sp.jedit.browser.VFSBrowser
import org.gjt.sp.jedit.io.{VFSManager, VFSFile}


class JEdit_Editor extends Editor[View]
{
  /* session */

  override def session: Session = PIDE.session

  def flush_edits(hidden: Boolean = false, purge: Boolean = false): Unit =
    GUI_Thread.require {
      val (doc_blobs, edits) = Document_Model.flush_edits(hidden, purge)
      session.update(doc_blobs, edits)
    }
  override def flush(): Unit = flush_edits()
  def purge(): Unit = flush_edits(purge = true)

  private val delay1_flush =
    Delay.last(PIDE.options.seconds("editor_input_delay"), gui = true) { flush() }

  private val delay2_flush =
    Delay.first(PIDE.options.seconds("editor_generated_input_delay"), gui = true) { flush() }

  def invoke(): Unit = delay1_flush.invoke()
  def invoke_generated(): Unit = { delay1_flush.invoke(); delay2_flush.invoke() }

  def shutdown(): Unit =
    GUI_Thread.require {
      delay1_flush.revoke()
      delay2_flush.revoke()
      Document_Model.flush_edits(hidden = false, purge = false)
    }

  def visible_node(name: Document.Node.Name): Boolean =
    (for {
      text_area <- JEdit_Lib.jedit_text_areas()
      doc_view <- Document_View.get(text_area)
    } yield doc_view.model.node_name).contains(name)


  /* current situation */

  override def current_node(view: View): Option[Document.Node.Name] =
    GUI_Thread.require { Document_Model.get(view.getBuffer).map(_.node_name) }

  override def current_node_snapshot(view: View): Option[Document.Snapshot] =
    GUI_Thread.require { Document_Model.get(view.getBuffer).map(_.snapshot()) }

  override def node_snapshot(name: Document.Node.Name): Document.Snapshot =
  {
    GUI_Thread.require {}
    Document_Model.get(name) match {
      case Some(model) => model.snapshot
      case None => session.snapshot(name)
    }
  }

  override def current_command(view: View, snapshot: Document.Snapshot): Option[Command] =
  {
    GUI_Thread.require {}

    val text_area = view.getTextArea
    val buffer = view.getBuffer

    Document_View.get(text_area) match {
      case Some(doc_view) if doc_view.model.is_theory =>
        snapshot.current_command(doc_view.model.node_name, text_area.getCaretPosition)
      case _ =>
        Document_Model.get(buffer) match {
          case Some(model) if !model.is_theory =>
            snapshot.version.nodes.commands_loading(model.node_name).headOption
          case _ => None
        }
    }
  }


  /* overlays */

  override def node_overlays(name: Document.Node.Name): Document.Node.Overlays =
    Document_Model.node_overlays(name)

  override def insert_overlay(command: Command, fn: String, args: List[String]): Unit =
    Document_Model.insert_overlay(command, fn, args)

  override def remove_overlay(command: Command, fn: String, args: List[String]): Unit =
    Document_Model.remove_overlay(command, fn, args)


  /* navigation */

  def push_position(view: View): Unit =
  {
    val navigator = jEdit.getPlugin("ise.plugin.nav.NavigatorPlugin")
    if (navigator != null) {
      try { Untyped.method(navigator.getClass, "pushPosition", view.getClass).invoke(null, view) }
      catch { case _: NoSuchMethodException => }
    }
  }

  def goto_buffer(focus: Boolean, view: View, buffer: Buffer, offset: Text.Offset): Unit =
  {
    GUI_Thread.require {}

    push_position(view)

    if (focus) view.goToBuffer(buffer) else view.showBuffer(buffer)
    try { view.getTextArea.moveCaretPosition(offset) }
    catch {
      case _: ArrayIndexOutOfBoundsException =>
      case _: IllegalArgumentException =>
    }
  }

  def goto_file(focus: Boolean, view: View, name: String): Unit =
    goto_file(focus, view, Line.Node_Position.offside(name))

  def goto_file(focus: Boolean, view: View, pos: Line.Node_Position): Unit =
  {
    GUI_Thread.require {}

    push_position(view)

    val name = pos.name
    val line = pos.line
    val column = pos.column

    JEdit_Lib.jedit_buffer(name) match {
      case Some(buffer) =>
        if (focus) view.goToBuffer(buffer) else view.showBuffer(buffer)
        val text_area = view.getTextArea

        try {
          val line_start = text_area.getBuffer.getLineStartOffset(line)
          text_area.moveCaretPosition(line_start)
          if (column > 0) text_area.moveCaretPosition(line_start + column)
        }
        catch {
          case _: ArrayIndexOutOfBoundsException =>
          case _: IllegalArgumentException =>
        }

      case None =>
        val is_dir =
          try {
            val vfs = VFSManager.getVFSForPath(name)
            val vfs_file = vfs._getFile((), name, view)
            vfs_file != null && vfs_file.getType == VFSFile.DIRECTORY
          }
          catch { case ERROR(_) => false }

        if (is_dir) VFSBrowser.browseDirectory(view, name)
        else if (!Isabelle_System.open_external_file(name)) {
          val args =
            if (line <= 0) Array(name)
            else if (column <= 0) Array(name, "+line:" + (line + 1))
            else Array(name, "+line:" + (line + 1) + "," + (column + 1))
          jEdit.openFiles(view, null, args)
        }
    }
  }

  def goto_doc(view: View, path: Path): Unit =
  {
    if (path.is_file)
      goto_file(true, view, File.platform_path(path))
    else {
      Isabelle_Thread.fork(name = "documentation") {
        try { Doc.view(path) }
        catch {
          case exn: Throwable =>
            GUI_Thread.later {
              GUI.error_dialog(view,
                "Documentation error", GUI.scrollable_text(Exn.message(exn)))
            }
        }
      }
    }
  }


  /* hyperlinks */

  def hyperlink_doc(name: String): Option[Hyperlink] =
    Doc.contents().collectFirst({
      case doc: Doc.Text_File if doc.name == name => doc.path
      case doc: Doc.Doc if doc.name == name => doc.path}).map(path =>
        new Hyperlink {
          override val external: Boolean = !path.is_file
          def follow(view: View): Unit = goto_doc(view, path)
          override def toString: String = "doc " + quote(name)
        })

  def hyperlink_url(name: String): Hyperlink =
    new Hyperlink {
      override val external = true
      def follow(view: View): Unit =
        Isabelle_Thread.fork(name = "hyperlink_url") {
          try { Isabelle_System.open(Url.escape_name(name)) }
          catch {
            case exn: Throwable =>
              GUI_Thread.later {
                GUI.error_dialog(view, "System error", GUI.scrollable_text(Exn.message(exn)))
              }
          }
        }
      override def toString: String = "URL " + quote(name)
    }

  def hyperlink_file(focus: Boolean, name: String): Hyperlink =
    hyperlink_file(focus, Line.Node_Position.offside(name))

  def hyperlink_file(focus: Boolean, pos: Line.Node_Position): Hyperlink =
    new Hyperlink {
      def follow(view: View): Unit = goto_file(focus, view, pos)
      override def toString: String = "file " + quote(pos.name)
    }

  def hyperlink_model(focus: Boolean, model: Document_Model, offset: Text.Offset): Hyperlink =
    model match {
      case file_model: File_Model =>
        val pos =
          try { file_model.node_position(offset) }
          catch { case ERROR(_) => Line.Node_Position(file_model.node_name.node) }
        hyperlink_file(focus, pos)
      case buffer_model: Buffer_Model =>
        new Hyperlink {
          def follow(view: View): Unit = goto_buffer(focus, view, buffer_model.buffer, offset)
          override def toString: String = "buffer " + quote(model.node_name.node)
        }
    }

  def hyperlink_source_file(focus: Boolean, source_name: String, line1: Int, offset: Symbol.Offset)
    : Option[Hyperlink] =
  {
    for (name <- PIDE.resources.source_file(source_name)) yield {
      def hyperlink(pos: Line.Position) =
        hyperlink_file(focus, Line.Node_Position(name, pos))

      if (offset > 0) {
        PIDE.resources.get_file_content(PIDE.resources.node_name(name)) match {
          case Some(text) =>
            hyperlink(
              (Line.Position.zero /:
                (Symbol.iterator(text).
                  zipWithIndex.takeWhile(p => p._2 < offset - 1).map(_._1)))(_.advance(_)))
          case None =>
            hyperlink(Line.Position((line1 - 1) max 0))
        }
      }
      else hyperlink(Line.Position((line1 - 1) max 0))
    }
  }

  override def hyperlink_command(
    focus: Boolean, snapshot: Document.Snapshot, id: Document_ID.Generic, offset: Symbol.Offset = 0)
      : Option[Hyperlink] =
  {
    if (snapshot.is_outdated) None
    else snapshot.find_command_position(id, offset).map(hyperlink_file(focus, _))
  }

  def is_hyperlink_position(snapshot: Document.Snapshot,
    text_offset: Text.Offset, pos: Position.T): Boolean =
  {
    pos match {
      case Position.Item_Id(id, range) if range.start > 0 =>
        snapshot.find_command(id) match {
          case Some((node, command)) if snapshot.get_node(command.node_name) eq node =>
            node.command_start(command) match {
              case Some(start) => text_offset == start + command.chunk.decode(range.start)
              case None => false
            }
          case _ => false
        }
      case _ => false
    }
  }

  def hyperlink_position(focus: Boolean, snapshot: Document.Snapshot, pos: Position.T)
      : Option[Hyperlink] =
    pos match {
      case Position.Item_File(name, line, range) =>
        hyperlink_source_file(focus, name, line, range.start)
      case Position.Item_Id(id, range) =>
        hyperlink_command(focus, snapshot, id, range.start)
      case _ => None
    }

  def hyperlink_def_position(focus: Boolean, snapshot: Document.Snapshot, pos: Position.T)
      : Option[Hyperlink] =
    pos match {
      case Position.Item_Def_File(name, line, range) =>
        hyperlink_source_file(focus, name, line, range.start)
      case Position.Item_Def_Id(id, range) =>
        hyperlink_command(focus, snapshot, id, range.start)
      case _ => None
    }


  /* dispatcher thread */

  override def assert_dispatcher[A](body: => A): A = GUI_Thread.assert(body)
  override def require_dispatcher[A](body: => A): A = GUI_Thread.require(body)
  override def send_dispatcher(body: => Unit): Unit = GUI_Thread.later(body)
  override def send_wait_dispatcher(body: => Unit): Unit = GUI_Thread.now(body)
}
