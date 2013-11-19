/*  Title:      Tools/jEdit/src/jedit_editor.scala
    Author:     Makarius

PIDE editor operations for jEdit.
*/

package isabelle.jedit


import isabelle._


import org.gjt.sp.jedit.{jEdit, View}


class JEdit_Editor extends Editor[View]
{
  /* session */

  override def session: Session = PIDE.session

  def document_models(): List[Document_Model] =
    for {
      buffer <- JEdit_Lib.jedit_buffers().toList
      model <- PIDE.document_model(buffer)
    } yield model

  def document_blobs(): Document.Blobs =
    document_models().filterNot(_.is_theory).map(model => (model.node_name -> model.blob())).toMap

  override def flush()
  {
    Swing_Thread.require()

    val edits = document_models().flatMap(_.flushed_edits())
    if (!edits.isEmpty) session.update(document_blobs(), edits)
  }

  private val delay_flush =
    Swing_Thread.delay_last(PIDE.options.seconds("editor_input_delay")) { flush() }

  def invoke(): Unit = Swing_Thread.require { delay_flush.invoke() }


  /* current situation */

  override def current_context: View =
    Swing_Thread.require { jEdit.getActiveView() }

  override def current_node(view: View): Option[Document.Node.Name] =
    Swing_Thread.require { PIDE.document_model(view.getBuffer).map(_.node_name) }

  override def current_node_snapshot(view: View): Option[Document.Snapshot] =
    Swing_Thread.require { PIDE.document_model(view.getBuffer).map(_.snapshot()) }

  override def node_snapshot(name: Document.Node.Name): Document.Snapshot =
  {
    Swing_Thread.require()

    JEdit_Lib.jedit_buffer(name.node) match {
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
    Swing_Thread.require()

    val text_area = view.getTextArea
    PIDE.document_view(text_area) match {
      case Some(doc_view) =>
        val node = snapshot.version.nodes(doc_view.model.node_name)
        val caret = snapshot.revert(text_area.getCaretPosition)
        if (caret < text_area.getBuffer.getLength) {
          val caret_commands = node.command_range(caret)
          if (caret_commands.hasNext) {
            val (cmd0, _) = caret_commands.next
            node.commands.reverse.iterator(cmd0).find(cmd => !cmd.is_ignored)
          }
          else None
        }
        else node.commands.reverse.iterator.find(cmd => !cmd.is_ignored)
      case None => None
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


  /* hyperlinks */

  def goto(view: View, file_name: String, line: Int = 0, column: Int = 0)
  {
    Swing_Thread.require()

    JEdit_Lib.jedit_buffer(file_name) match {
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

      case None =>
        val args =
          if (line <= 0) Array(file_name)
          else if (column <= 0) Array(file_name, "+line:" + line.toInt)
          else Array(file_name, "+line:" + line.toInt + "," + column.toInt)
        jEdit.openFiles(view, null, args)
    }
  }

  override def hyperlink_file(file_name: String, line: Int = 0, column: Int = 0): Hyperlink =
    new Hyperlink { def follow(view: View) = goto(view, file_name, line, column) }

  override def hyperlink_command(snapshot: Document.Snapshot, command: Command, offset: Int = 0)
    : Option[Hyperlink] =
  {
    if (snapshot.is_outdated) None
    else {
      snapshot.state.find_command(snapshot.version, command.id) match {
        case None => None
        case Some((node, _)) =>
          val file_name = command.node_name.node
          val sources =
            node.commands.iterator.takeWhile(_ != command).map(_.source) ++
              (if (offset == 0) Iterator.empty
               else Iterator.single(command.source(Text.Range(0, command.decode(offset)))))
          val (line, column) = ((1, 1) /: sources)(Symbol.advance_line_column)
          Some(new Hyperlink { def follow(view: View) { goto(view, file_name, line, column) } })
      }
    }
  }
}
