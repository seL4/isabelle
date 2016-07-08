/*  Title:      Tools/jEdit/src/text_structure.scala
    Author:     Makarius

Text structure based on Isabelle/Isar outer syntax.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.indent.{IndentRule, IndentAction}
import org.gjt.sp.jedit.textarea.{TextArea, StructureMatcher, Selection}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.Buffer


object Text_Structure
{
  /* token navigator */

  class Navigator(syntax: Outer_Syntax, buffer: Buffer)
  {
    val limit = PIDE.options.value.int("jedit_structure_limit") max 0

    def iterator(line: Int, lim: Int = limit): Iterator[Text.Info[Token]] =
      Token_Markup.line_token_iterator(syntax, buffer, line, line + lim).
        filter(_.info.is_proper)

    def reverse_iterator(line: Int, lim: Int = limit): Iterator[Text.Info[Token]] =
      Token_Markup.line_token_reverse_iterator(syntax, buffer, line, line - lim).
        filter(_.info.is_proper)
  }


  /* indentation */

  object Indent_Rule extends IndentRule
  {
    def apply(buffer: JEditBuffer, line: Int, prev_line: Int, prev_prev_line: Int,
      actions: java.util.List[IndentAction])
    {
      Isabelle.buffer_syntax(buffer) match {
        case Some(syntax) if buffer.isInstanceOf[Buffer] =>
          val keywords = syntax.keywords
          val nav = new Navigator(syntax, buffer.asInstanceOf[Buffer])

          val indent = 0  // FIXME

          actions.clear()
          actions.add(new IndentAction.AlignOffset(indent))
        case _ =>
      }
    }
  }


  /* structure matching */

  object Matcher extends StructureMatcher
  {
    private def find_block(
      open: Token => Boolean,
      close: Token => Boolean,
      reset: Token => Boolean,
      restrict: Token => Boolean,
      it: Iterator[Text.Info[Token]]): Option[(Text.Range, Text.Range)] =
    {
      val range1 = it.next.range
      it.takeWhile(info => !info.info.is_command || restrict(info.info)).
        scanLeft((range1, 1))(
          { case ((r, d), Text.Info(range, tok)) =>
              if (open(tok)) (range, d + 1)
              else if (close(tok)) (range, d - 1)
              else if (reset(tok)) (range, 0)
              else (r, d) }
        ).collectFirst({ case (range2, 0) => (range1, range2) })
    }

    private def find_pair(text_area: TextArea): Option[(Text.Range, Text.Range)] =
    {
      val buffer = text_area.getBuffer
      val caret_line = text_area.getCaretLine
      val caret = text_area.getCaretPosition

      Isabelle.buffer_syntax(text_area.getBuffer) match {
        case Some(syntax) if buffer.isInstanceOf[Buffer] =>
          val keywords = syntax.keywords

          val nav = new Navigator(syntax, buffer.asInstanceOf[Buffer])

          def caret_iterator(): Iterator[Text.Info[Token]] =
            nav.iterator(caret_line).dropWhile(info => !info.range.touches(caret))

          def reverse_caret_iterator(): Iterator[Text.Info[Token]] =
            nav.reverse_iterator(caret_line).dropWhile(info => !info.range.touches(caret))

          nav.iterator(caret_line, 1).find(info => info.range.touches(caret))
          match {
            case Some(Text.Info(range1, tok)) if keywords.is_command(tok, Keyword.theory_goal) =>
              find_block(
                keywords.is_command(_, Keyword.proof_goal),
                keywords.is_command(_, Keyword.qed),
                keywords.is_command(_, Keyword.qed_global),
                t =>
                  keywords.is_command(t, Keyword.diag) ||
                  keywords.is_command(t, Keyword.proof),
                caret_iterator())

            case Some(Text.Info(range1, tok)) if keywords.is_command(tok, Keyword.proof_goal) =>
              find_block(
                keywords.is_command(_, Keyword.proof_goal),
                keywords.is_command(_, Keyword.qed),
                _ => false,
                t =>
                  keywords.is_command(t, Keyword.diag) ||
                  keywords.is_command(t, Keyword.proof),
                caret_iterator())

            case Some(Text.Info(range1, tok)) if keywords.is_command(tok, Keyword.qed_global) =>
              reverse_caret_iterator().find(info => keywords.is_command(info.info, Keyword.theory))
              match {
                case Some(Text.Info(range2, tok))
                if keywords.is_command(tok, Keyword.theory_goal) => Some((range1, range2))
                case _ => None
              }

            case Some(Text.Info(range1, tok)) if keywords.is_command(tok, Keyword.qed) =>
              find_block(
                keywords.is_command(_, Keyword.qed),
                t =>
                  keywords.is_command(t, Keyword.proof_goal) ||
                  keywords.is_command(t, Keyword.theory_goal),
                _ => false,
                t =>
                  keywords.is_command(t, Keyword.diag) ||
                  keywords.is_command(t, Keyword.proof) ||
                  keywords.is_command(t, Keyword.theory_goal),
                reverse_caret_iterator())

            case Some(Text.Info(range1, tok)) if tok.is_begin =>
              find_block(_.is_begin, _.is_end, _ => false, _ => true, caret_iterator())

            case Some(Text.Info(range1, tok)) if tok.is_end =>
              find_block(_.is_end, _.is_begin, _ => false, _ => true, reverse_caret_iterator())
              match {
                case Some((_, range2)) =>
                  reverse_caret_iterator().
                    dropWhile(info => info.range != range2).
                    dropWhile(info => info.range == range2).
                    find(info => info.info.is_command || info.info.is_begin)
                  match {
                    case Some(Text.Info(range3, tok)) =>
                      if (keywords.is_command(tok, Keyword.theory_block)) Some((range1, range3))
                      else Some((range1, range2))
                    case None => None
                  }
                case None => None
              }

            case _ => None
          }
        case _ => None
      }
    }

    def getMatch(text_area: TextArea): StructureMatcher.Match =
      find_pair(text_area) match {
        case Some((_, range)) =>
          val line = text_area.getBuffer.getLineOfOffset(range.start)
          new StructureMatcher.Match(Matcher, line, range.start, line, range.stop)
        case None => null
      }

    def selectMatch(text_area: TextArea)
    {
      def get_span(offset: Text.Offset): Option[Text.Range] =
        for {
          syntax <- Isabelle.buffer_syntax(text_area.getBuffer)
          span <- Token_Markup.command_span(syntax, text_area.getBuffer, offset)
        } yield span.range

      find_pair(text_area) match {
        case Some((r1, r2)) =>
          (get_span(r1.start), get_span(r2.start)) match {
            case (Some(range1), Some(range2)) =>
              val start = range1.start min range2.start
              val stop = range1.stop max range2.stop

              text_area.moveCaretPosition(stop, false)
              if (!text_area.isMultipleSelectionEnabled) text_area.selectNone
              text_area.addToSelection(new Selection.Range(start, stop))
            case _ =>
          }
        case None =>
      }
    }
  }
}
