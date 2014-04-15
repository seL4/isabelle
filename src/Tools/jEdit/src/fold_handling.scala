/*  Title:      Tools/jEdit/src/fold_handling.scala
    Author:     Makarius

Handling of folds within the text structure.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.buffer.{JEditBuffer, FoldHandler}

import javax.swing.text.Segment


object Fold_Handling
{
  class Document_Fold_Handler(private val rendering: Rendering)
    extends FoldHandler("isabelle-document")
  {
    override def equals(other: Any): Boolean =
      other match {
        case that: Document_Fold_Handler => this.rendering == that.rendering
        case _ => false
      }

    override def getFoldLevel(buffer: JEditBuffer, line: Int, seg: Segment): Int =
    {
      def depth(i: Text.Offset): Int =
        if (i < 0) 0
        else {
          rendering.fold_depth(Text.Range(i, i + 1)).map(_.info) match {
            case d :: _ => d
            case _ => 0
          }
        }

      if (line <= 0) 0
      else {
        val range = JEdit_Lib.line_range(buffer, line - 1)
        buffer.getFoldLevel(line - 1) - depth(range.start - 1) + depth(range.stop - 1)
      }
    }
  }
}

