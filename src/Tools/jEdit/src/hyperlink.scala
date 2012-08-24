/*  Title:      Tools/jEdit/src/hyperlink.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Hyperlinks within jEdit buffers for PIDE proof documents.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.{View, jEdit}
import org.gjt.sp.jedit.textarea.JEditTextArea


object Hyperlink
{
  def apply(jedit_file: String, line: Int, column: Int): Hyperlink =
    File_Link(jedit_file, line, column)
}

abstract class Hyperlink
{
  def follow(view: View): Unit
}

private case class File_Link(jedit_file: String, line: Int, column: Int) extends Hyperlink
{
  override def follow(view: View)
  {
    Swing_Thread.require()

    Isabelle.jedit_buffer(jedit_file) match {
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
          if (line <= 0) Array(jedit_file)
          else if (column <= 0) Array(jedit_file, "+line:" + line.toInt)
          else Array(jedit_file, "+line:" + line.toInt + "," + column.toInt)
        jEdit.openFiles(view, null, args)
    }
  }
}

