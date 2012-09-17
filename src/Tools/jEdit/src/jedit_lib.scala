/*  Title:      Tools/jEdit/src/jedit_lib.scala
    Author:     Makarius

Misc library functions for jEdit.
*/

package isabelle.jedit


import isabelle._


import org.gjt.sp.jedit.{jEdit, Buffer, View}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea}


object JEdit_Lib
{
  /* buffers */

  def swing_buffer_lock[A](buffer: JEditBuffer)(body: => A): A =
    Swing_Thread.now { buffer_lock(buffer) { body } }

  def buffer_text(buffer: JEditBuffer): String =
    buffer_lock(buffer) { buffer.getText(0, buffer.getLength) }

  def buffer_name(buffer: Buffer): String = buffer.getSymlinkPath

  def buffer_node_dummy(buffer: Buffer): Option[Document.Node.Name] =
    Some(Document.Node.Name(buffer_name(buffer), buffer.getDirectory, buffer.getName))

  def buffer_node_name(buffer: Buffer): Option[Document.Node.Name] =
  {
    val name = buffer_name(buffer)
    Thy_Header.thy_name(name).map(theory => Document.Node.Name(name, buffer.getDirectory, theory))
  }


  /* main jEdit components */

  def jedit_buffers(): Iterator[Buffer] = jEdit.getBuffers().iterator

  def jedit_buffer(name: String): Option[Buffer] =
    jedit_buffers().find(buffer => buffer_name(buffer) == name)

  def jedit_views(): Iterator[View] = jEdit.getViews().iterator

  def jedit_text_areas(view: View): Iterator[JEditTextArea] =
    view.getEditPanes().iterator.map(_.getTextArea)

  def jedit_text_areas(): Iterator[JEditTextArea] =
    jedit_views().flatMap(jedit_text_areas(_))

  def jedit_text_areas(buffer: JEditBuffer): Iterator[JEditTextArea] =
    jedit_text_areas().filter(_.getBuffer == buffer)

  def buffer_lock[A](buffer: JEditBuffer)(body: => A): A =
  {
    try { buffer.readLock(); body }
    finally { buffer.readUnlock() }
  }


  /* point range */

  def point_range(buffer: JEditBuffer, offset: Text.Offset): Text.Range =
    buffer_lock(buffer) {
      def text(i: Text.Offset): Char = buffer.getText(i, 1).charAt(0)
      try {
        val c = text(offset)
        if (Character.isHighSurrogate(c) && Character.isLowSurrogate(text(offset + 1)))
          Text.Range(offset, offset + 2)
        else if (Character.isLowSurrogate(c) && Character.isHighSurrogate(text(offset - 1)))
          Text.Range(offset - 1, offset + 1)
        else Text.Range(offset, offset + 1)
      }
      catch { case _: ArrayIndexOutOfBoundsException => Text.Range(offset, offset + 1) }
    }


  /* proper line range */

  // NB: TextArea.getScreenLineEndOffset of last line is beyond Buffer.getLength
  def proper_line_range(buffer: JEditBuffer, start: Text.Offset, end: Text.Offset): Text.Range =
    Text.Range(start, end min buffer.getLength)


  /* visible text range */

  def visible_range(text_area: TextArea): Option[Text.Range] =
  {
    val buffer = text_area.getBuffer
    val n = text_area.getVisibleLines
    if (n > 0) {
      val start = text_area.getScreenLineStartOffset(0)
      val raw_end = text_area.getScreenLineEndOffset(n - 1)
      Some(proper_line_range(buffer, start, if (raw_end >= 0) raw_end else buffer.getLength))
    }
    else None
  }

  def invalidate_range(text_area: TextArea, range: Text.Range)
  {
    val buffer = text_area.getBuffer
    text_area.invalidateLineRange(
      buffer.getLineOfOffset(range.start),
      buffer.getLineOfOffset(range.stop))
  }
}

