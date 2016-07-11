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
    private val keyword_open = Keyword.theory_goal ++ Keyword.proof_open
    private val keyword_close = Keyword.proof_close

    def apply(buffer: JEditBuffer, current_line: Int, prev_line: Int, prev_prev_line: Int,
      actions: java.util.List[IndentAction])
    {
      Isabelle.buffer_syntax(buffer) match {
        case Some(syntax) if buffer.isInstanceOf[Buffer] =>
          val keywords = syntax.keywords
          val nav = new Navigator(syntax, buffer.asInstanceOf[Buffer])

          def head_token(line: Int): Option[Token] =
            nav.iterator(line, 1).toStream.headOption.map(_.info)

          def head_is_quasi_command(line: Int): Boolean =
            head_token(line) match {
              case None => false
              case Some(tok) => keywords.is_quasi_command(tok)
            }

          def prev_command: Option[Token] =
            nav.reverse_iterator(prev_line, 1).
              collectFirst({ case Text.Info(_, tok) if tok.is_command => tok })

          def prev_span: Iterator[Token] =
            nav.reverse_iterator(prev_line).map(_.info).takeWhile(tok => !tok.is_command)


          def line_indent(line: Int): Int =
            if (line < 0 || line >= buffer.getLineCount) 0
            else buffer.getCurrentIndentForLine(line, null)

          val indent_size = buffer.getIndentSize

          def indent_indent(tok: Token): Int =
            if (keywords.is_command(tok, keyword_open)) indent_size
            else if (keywords.is_command(tok, keyword_close)) - indent_size
            else 0

          def indent_offset(tok: Token): Int =
            if (keywords.is_command(tok, Keyword.proof_enclose)) indent_size
            else 0

          def indent_extra: Int =
            if (prev_span.exists(keywords.is_quasi_command(_))) indent_size
            else 0

          def indent_structure: Int =
            nav.reverse_iterator(current_line - 1).scanLeft((0, false))(
              { case ((ind, _), Text.Info(range, tok)) =>
                  val ind1 = ind + indent_indent(tok)
                  if (tok.is_command) {
                    val line = buffer.getLineOfOffset(range.start)
                    if (head_token(line) == Some(tok))
                      (ind1 + indent_offset(tok) + line_indent(line), true)
                    else (ind1, false)
                  }
                  else (ind1, false)
              }).collectFirst({ case (i, true) => i }).getOrElse(0)

          val indent =
            head_token(current_line) match {
              case None => indent_structure + indent_extra
              case Some(tok) =>
                if (keywords.is_command(tok, Keyword.theory)) 0
                else if (tok.is_command) indent_structure - indent_offset(tok)
                else {
                  prev_command match {
                    case None =>
                      val extra =
                        (keywords.is_quasi_command(tok), head_is_quasi_command(prev_line)) match {
                          case (true, true) | (false, false) => 0
                          case (true, false) => - indent_extra
                          case (false, true) => indent_extra
                        }
                      line_indent(prev_line) + extra
                    case Some(prev_tok) =>
                      indent_structure - indent_offset(prev_tok) -
                      indent_indent(prev_tok) + indent_size
                  }
               }
            }

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
