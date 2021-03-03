/*  Title:      Tools/jEdit/src/fold_handling.scala
    Author:     Makarius

Handling of folds within the text structure.
*/

package isabelle.jedit


import isabelle._

import javax.swing.text.Segment

import scala.jdk.CollectionConverters._

import org.gjt.sp.jedit.buffer.{JEditBuffer, FoldHandler}


object Fold_Handling
{
  /* input: dynamic line context  */

  class Fold_Handler extends FoldHandler("isabelle")
  {
    override def equals(other: Any): Boolean =
      other match {
        case that: Fold_Handler => true
        case _ => false
      }

    override def getFoldLevel(buffer: JEditBuffer, line: Int, seg: Segment): Int =
      Token_Markup.Line_Context.after(buffer, line).structure.depth max 0

    override def getPrecedingFoldLevels(
      buffer: JEditBuffer, line: Int, seg: Segment, level: Int): java.util.List[Integer] =
    {
      val structure = Token_Markup.Line_Context.after(buffer, line).structure
      val result =
        if (line > 0 && structure.command)
          Range.inclusive(line - 1, 0, -1).iterator.
            map(i => Token_Markup.Line_Context.after(buffer, i).structure).
            takeWhile(_.improper).map(_ => structure.depth max 0).toList
        else Nil

      if (result.isEmpty) null else result.map(Integer.valueOf).asJava
    }
  }


  /* output: static document rendering */

  class Document_Fold_Handler(private val rendering: JEdit_Rendering)
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
          rendering.fold_depth(Text.Range(i, i + 1)) match {
            case Text.Info(_, d) :: _ => d
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
