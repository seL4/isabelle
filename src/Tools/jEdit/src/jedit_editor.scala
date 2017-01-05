/*  Title:      Tools/jEdit/src/jedit_editor.scala
    Author:     Makarius

PIDE editor operations for jEdit.
*/

package isabelle.jedit


import isabelle._


import java.io.{File => JFile}

import org.gjt.sp.jedit.{jEdit, View, Buffer}
import org.gjt.sp.jedit.browser.VFSBrowser


class JEdit_Editor extends Editor[View]
{
  /* session */

  override def session: Session = PIDE.session

  // owned by GUI thread
  private var removed_nodes = Set.empty[Document.Node.Name]

  def remove_node(name: Document.Node.Name): Unit =
    GUI_Thread.require { removed_nodes += name }

  override def flush(hidden: Boolean = false)
  {
    GUI_Thread.require {}

    val doc_blobs = PIDE.document_blobs()
    val models = PIDE.document_models()

    val removed = removed_nodes; removed_nodes = Set.empty
    val removed_perspective =
      (removed -- models.iterator.map(_.node_name)).toList.map(
        name => (name, Document.Node.no_perspective_text))

    val edits = models.flatMap(_.flushed_edits(hidden, doc_blobs)) ::: removed_perspective
    session.update(doc_blobs, edits)
  }

  private val delay1_flush =
    GUI_Thread.delay_last(PIDE.options.seconds("editor_input_delay")) { flush() }

  private val delay2_flush =
    GUI_Thread.delay_first(PIDE.options.seconds("editor_generated_input_delay")) { flush() }

  def invoke(): Unit = delay1_flush.invoke()
  def invoke_generated(): Unit = { delay1_flush.invoke(); delay2_flush.invoke() }

  def stable_tip_version(): Option[Document.Version] =
    GUI_Thread.require {
      if (removed_nodes.isEmpty && PIDE.document_models().forall(_.is_stable))
        session.current_state().stable_tip_version
      else None
    }

  def visible_node(name: Document.Node.Name): Boolean =
    JEdit_Lib.jedit_buffer(name) match {
      case Some(buffer) => JEdit_Lib.jedit_text_areas(buffer).nonEmpty
      case None => false
    }


  /* current situation */

  override def current_context: View =
    GUI_Thread.require { jEdit.getActiveView() }

  override def current_node(view: View): Option[Document.Node.Name] =
    GUI_Thread.require { PIDE.document_model(view.getBuffer).map(_.node_name) }

  override def current_node_snapshot(view: View): Option[Document.Snapshot] =
    GUI_Thread.require { PIDE.document_model(view.getBuffer).map(_.snapshot()) }

  override def node_snapshot(name: Document.Node.Name): Document.Snapshot =
  {
    GUI_Thread.require {}

    JEdit_Lib.jedit_buffer(name) match {
      case Some(buffer) =>
        PIDE.document_model(buffer) match {
          case Some(model) => model.snapshot
          case None => session.snapshot(name)
        }
      case None => session.snapshot(name)
    }
  }

  override def current_command(view: View, snapshot: Document.Snapshot): Option[Command] =
  {
    GUI_Thread.require {}

    val text_area = view.getTextArea
    val buffer = view.getBuffer

    PIDE.document_view(text_area) match {
      case Some(doc_view) if doc_view.model.is_theory =>
        val node = snapshot.version.nodes(doc_view.model.node_name)
        val caret = snapshot.revert(text_area.getCaretPosition)
        if (caret < buffer.getLength) {
          val caret_command_iterator = node.command_iterator(caret)
          if (caret_command_iterator.hasNext) {
            val (cmd0, _) = caret_command_iterator.next
            node.commands.reverse.iterator(cmd0).find(cmd => !cmd.is_ignored)
          }
          else None
        }
        else node.commands.reverse.iterator.find(cmd => !cmd.is_ignored)
      case _ =>
        PIDE.document_model(buffer) match {
          case Some(model) if !model.is_theory =>
            snapshot.version.nodes.commands_loading(model.node_name) match {
              case cmd :: _ => Some(cmd)
              case Nil => None
            }
          case _ => None
        }
    }
  }


  /* overlays */

  private val overlays = Synchronized(Document.Overlays.empty)

  override def node_overlays(name: Document.Node.Name): Document.Node.Overlays =
    overlays.value(name)

  override def insert_overlay(command: Command, fn: String, args: List[String]): Unit =
    overlays.change(_.insert(command, fn, args))

  override def remove_overlay(command: Command, fn: String, args: List[String]): Unit =
    overlays.change(_.remove(command, fn, args))


  /* navigation */

  def push_position(view: View)
  {
    val navigator = jEdit.getPlugin("ise.plugin.nav.NavigatorPlugin")
    if (navigator != null) {
      try { Untyped.method(navigator.getClass, "pushPosition", view.getClass).invoke(null, view) }
      catch { case _: NoSuchMethodException => }
    }
  }

  def goto_buffer(focus: Boolean, view: View, buffer: Buffer, offset: Text.Offset)
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
    goto_file(focus, view, Line.Node_Position(name))

  def goto_file(focus: Boolean, view: View, pos: Line.Node_Position)
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

      case None if (new JFile(name)).isDirectory =>
        VFSBrowser.browseDirectory(view, name)

      case None =>
        val args =
          if (line <= 0) Array(name)
          else if (column <= 0) Array(name, "+line:" + (line + 1))
          else Array(name, "+line:" + (line + 1) + "," + (column + 1))
        jEdit.openFiles(view, null, args)
    }
  }

  def goto_doc(view: View, path: Path)
  {
    if (path.is_file)
      goto_file(true, view, File.platform_path(path))
    else {
      Standard_Thread.fork("documentation") {
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
          override val external = !path.is_file
          def follow(view: View): Unit = goto_doc(view, path)
          override def toString: String = "doc " + quote(name)
        })

  def hyperlink_url(name: String): Hyperlink =
    new Hyperlink {
      override val external = true
      def follow(view: View): Unit =
        Standard_Thread.fork("hyperlink_url") {
          try { Isabelle_System.open(Url.escape(name)) }
          catch {
            case exn: Throwable =>
              GUI_Thread.later {
                GUI.error_dialog(view, "System error", GUI.scrollable_text(Exn.message(exn)))
              }
          }
        }
      override def toString: String = "URL " + quote(name)
    }

  def hyperlink_buffer(focus: Boolean, buffer: Buffer, offset: Text.Offset): Hyperlink =
    new Hyperlink {
      def follow(view: View): Unit = goto_buffer(focus, view, buffer, offset)
      override def toString: String = "buffer " + quote(JEdit_Lib.buffer_name(buffer))
    }

  def hyperlink_file(focus: Boolean, name: String): Hyperlink =
    hyperlink_file(focus, Line.Node_Position(name))

  def hyperlink_file(focus: Boolean, pos: Line.Node_Position): Hyperlink =
    new Hyperlink {
      def follow(view: View): Unit = goto_file(focus, view, pos)
      override def toString: String = "file " + quote(pos.name)
    }

  def hyperlink_source_file(focus: Boolean, source_name: String, line1: Int, offset: Symbol.Offset)
    : Option[Hyperlink] =
  {
    for (name <- PIDE.resources.source_file(source_name)) yield {
      JEdit_Lib.jedit_buffer(name) match {
        case Some(buffer) if offset > 0 =>
          val pos =
            JEdit_Lib.buffer_lock(buffer) {
              (Line.Position.zero /:
                (Symbol.iterator(JEdit_Lib.buffer_text(buffer)).
                  zipWithIndex.takeWhile(p => p._2 < offset - 1).
                  map(_._1)))(_.advance(_, Text.Length))
            }
          hyperlink_file(focus, Line.Node_Position(name, pos))
        case _ =>
          hyperlink_file(focus, Line.Node_Position(name, Line.Position((line1 - 1) max 0)))
      }
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
          case Some((node, command)) if snapshot.version.nodes(command.node_name) eq node =>
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
}
