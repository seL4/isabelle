/*  Title:      Tools/jEdit/src/jedit_editor.scala
    Author:     Makarius

PIDE editor operations for jEdit.
*/

package isabelle.jedit


import isabelle._


import java.io.{File => JFile}

import org.gjt.sp.jedit.{jEdit, View}
import org.gjt.sp.jedit.browser.VFSBrowser


class JEdit_Editor extends Editor[View]
{
  /* session */

  override def session: Session = PIDE.session

  // owned by GUI thread
  private var removed_nodes = Set.empty[Document.Node.Name]

  def remove_node(name: Document.Node.Name): Unit =
    GUI_Thread.require { removed_nodes += name }

  override def flush()
  {
    GUI_Thread.require {}

    val doc_blobs = PIDE.document_blobs()
    val models = PIDE.document_models()

    val removed = removed_nodes; removed_nodes = Set.empty
    val removed_perspective =
      (removed -- models.iterator.map(_.node_name)).toList.map(
        name => (name, Document.Node.empty_perspective_text))

    val edits = models.flatMap(_.flushed_edits(doc_blobs)) ::: removed_perspective
    if (!edits.isEmpty) session.update(doc_blobs, edits)
  }

  private val delay_flush =
    GUI_Thread.delay_last(PIDE.options.seconds("editor_input_delay")) { flush() }

  def invoke(): Unit = delay_flush.invoke()


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
            snapshot.version.nodes.load_commands(model.node_name) match {
              case cmd :: _ => Some(cmd)
              case Nil => None
            }
          case _ => None
        }
    }
  }


  /* overlays */

  private var overlays = Document.Overlays.empty

  override def node_overlays(name: Document.Node.Name): Document.Node.Overlays =
    synchronized { overlays(name) }

  override def insert_overlay(command: Command, fn: String, args: List[String]): Unit =
    synchronized { overlays = overlays.insert(command, fn, args) }

  override def remove_overlay(command: Command, fn: String, args: List[String]): Unit =
    synchronized { overlays = overlays.remove(command, fn, args) }


  /* navigation */

  def push_position(view: View)
  {
    val navigator = jEdit.getPlugin("ise.plugin.nav.NavigatorPlugin")
    if (navigator != null) {
      try {
        val m = navigator.getClass.getDeclaredMethod("pushPosition", view.getClass)
        m.invoke(null, view)
      }
      catch { case _: NoSuchMethodException => }
    }
  }

  def goto_file(view: View, name: String, line: Int = 0, column: Int = 0)
  {
    GUI_Thread.require {}

    push_position(view)

    JEdit_Lib.jedit_buffer(name) match {
      case Some(buffer) =>
        view.goToBuffer(buffer)
        val text_area = view.getTextArea

        try {
          val line_start = text_area.getBuffer.getLineStartOffset(line - 1)
          text_area.moveCaretPosition(line_start)
          if (column > 0) text_area.moveCaretPosition(line_start + column - 1)
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
          else if (column <= 0) Array(name, "+line:" + line.toInt)
          else Array(name, "+line:" + line.toInt + "," + column.toInt)
        jEdit.openFiles(view, null, args)
    }
  }


  /* hyperlinks */

  def hyperlink_url(name: String): Hyperlink =
    new Hyperlink {
      val external = true
      def follow(view: View): Unit =
        Future.fork {
          try { Isabelle_System.open(name) }
          catch {
            case exn: Throwable =>
              GUI.error_dialog(view, "System error", GUI.scrollable_text(Exn.message(exn)))
          }
        }
      override def toString: String = "URL " + quote(name)
    }

  def hyperlink_file(name: String, line: Int = 0, column: Int = 0): Hyperlink =
    new Hyperlink {
      val external = false
      def follow(view: View): Unit = goto_file(view, name, line, column)
      override def toString: String = "file " + quote(name)
    }

  def hyperlink_source_file(source_name: String, line: Int, offset: Symbol.Offset)
    : Option[Hyperlink] =
  {
    val opt_name =
      if (Path.is_wellformed(source_name)) {
        if (Path.is_valid(source_name)) {
          val path = Path.explode(source_name)
          Some(Isabelle_System.platform_path(Isabelle_System.source_file(path) getOrElse path))
        }
        else None
      }
      else Some(source_name)

    opt_name match {
      case Some(name) =>
        JEdit_Lib.jedit_buffer(name) match {
          case Some(buffer) if offset > 0 =>
            val (line, column) =
              JEdit_Lib.buffer_lock(buffer) {
                ((1, 1) /:
                  (Symbol.iterator(JEdit_Lib.buffer_text(buffer)).
                    zipWithIndex.takeWhile(p => p._2 < offset - 1).map(_._1)))(
                      Symbol.advance_line_column)
              }
            Some(hyperlink_file(name, line, column))
          case _ => Some(hyperlink_file(name, line))
        }
      case None => None
    }
  }

  override def hyperlink_command(
    snapshot: Document.Snapshot, command: Command, offset: Symbol.Offset = 0): Option[Hyperlink] =
  {
    if (snapshot.is_outdated) None
    else {
      snapshot.state.find_command(snapshot.version, command.id) match {
        case None => None
        case Some((node, _)) =>
          val file_name = command.node_name.node
          val sources_iterator =
            node.commands.iterator.takeWhile(_ != command).map(_.source) ++
              (if (offset == 0) Iterator.empty
               else Iterator.single(command.source(Text.Range(0, command.chunk.decode(offset)))))
          val (line, column) = ((1, 1) /: sources_iterator)(Symbol.advance_line_column)
          Some(hyperlink_file(file_name, line, column))
      }
    }
  }

  def hyperlink_command_id(
    snapshot: Document.Snapshot,
    id: Document_ID.Generic,
    offset: Symbol.Offset): Option[Hyperlink] =
  {
    snapshot.state.find_command(snapshot.version, id) match {
      case Some((node, command)) => hyperlink_command(snapshot, command, offset)
      case None => None
    }
  }
}
