/*  Title:      Tools/jEdit/src/hyperlink.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Hyperlinks within jEdit buffers for PIDE proof documents.
*/

package isabelle.jedit


import isabelle._

import java.io.{File => JFile}

import org.gjt.sp.jedit.{View, jEdit}
import org.gjt.sp.jedit.textarea.JEditTextArea


object Hyperlink
{
  def apply(file: JFile, line: Int, column: Int): Hyperlink =
    File_Link(file, line, column)
}

abstract class Hyperlink
{
  def follow(view: View): Unit
}

private case class File_Link(file: JFile, line: Int, column: Int) extends Hyperlink
{
  override def follow(view: View)
  {
    Swing_Thread.require()

    val full_name = file.getCanonicalPath
    val base_name = file.getName

    Isabelle.jedit_buffer(full_name) match {
      case Some(buffer) =>
        view.setBuffer(buffer)
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
          if (line <= 0) Array(base_name)
          else if (column <= 0) Array(base_name, "+line:" + line.toInt)
          else Array(base_name, "+line:" + line.toInt + "," + column.toInt)
        jEdit.openFiles(view, file.getParent, args)
    }
  }
}

