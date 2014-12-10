/*  Title:      Tools/jEdit/src/structure_matching.scala
    Author:     Makarius

Structure matcher for Isabelle/Isar outer syntax.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.textarea.{TextArea, StructureMatcher, Selection}


object Structure_Matching
{
  object Isabelle_Matcher extends StructureMatcher
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
        case Some(syntax) =>
          val limit = PIDE.options.value.int("jedit_structure_limit") max 0

          def is_command_kind(token: Token, pred: String => Boolean): Boolean =
            token.is_command_kind(syntax.keywords, pred)

          def iterator(line: Int, lim: Int = limit): Iterator[Text.Info[Token]] =
            Token_Markup.line_token_iterator(syntax, buffer, line, line + lim).
              filter(_.info.is_proper)

          def rev_iterator(line: Int, lim: Int = limit): Iterator[Text.Info[Token]] =
            Token_Markup.line_token_reverse_iterator(syntax, buffer, line, line - lim).
              filter(_.info.is_proper)

          def caret_iterator(): Iterator[Text.Info[Token]] =
            iterator(caret_line).dropWhile(info => !info.range.touches(caret))

          def rev_caret_iterator(): Iterator[Text.Info[Token]] =
            rev_iterator(caret_line).dropWhile(info => !info.range.touches(caret))

          iterator(caret_line, 1).find(info => info.range.touches(caret))
          match {
            case Some(Text.Info(range1, tok)) if is_command_kind(tok, Keyword.theory_goal) =>
              find_block(
                is_command_kind(_, Keyword.proof_goal),
                is_command_kind(_, Keyword.qed),
                is_command_kind(_, Keyword.qed_global),
                t =>
                  is_command_kind(t, Keyword.diag) ||
                  is_command_kind(t, Keyword.proof),
                caret_iterator())

            case Some(Text.Info(range1, tok)) if is_command_kind(tok, Keyword.proof_goal) =>
              find_block(
                is_command_kind(_, Keyword.proof_goal),
                is_command_kind(_, Keyword.qed),
                _ => false,
                t =>
                  is_command_kind(t, Keyword.diag) ||
                  is_command_kind(t, Keyword.proof),
                caret_iterator())

            case Some(Text.Info(range1, tok)) if is_command_kind(tok, Keyword.qed_global) =>
              rev_caret_iterator().find(info => is_command_kind(info.info, Keyword.theory))
              match {
                case Some(Text.Info(range2, tok))
                if is_command_kind(tok, Keyword.theory_goal) => Some((range1, range2))
                case _ => None
              }

            case Some(Text.Info(range1, tok)) if is_command_kind(tok, Keyword.qed) =>
              find_block(
                is_command_kind(_, Keyword.qed),
                t =>
                  is_command_kind(t, Keyword.proof_goal) ||
                  is_command_kind(t, Keyword.theory_goal),
                _ => false,
                t =>
                  is_command_kind(t, Keyword.diag) ||
                  is_command_kind(t, Keyword.proof) ||
                  is_command_kind(t, Keyword.theory_goal),
                rev_caret_iterator())

            case Some(Text.Info(range1, tok)) if tok.is_begin =>
              find_block(_.is_begin, _.is_end, _ => false, _ => true, caret_iterator())

            case Some(Text.Info(range1, tok)) if tok.is_end =>
              find_block(_.is_end, _.is_begin, _ => false, _ => true, rev_caret_iterator())
              match {
                case Some((_, range2)) =>
                  rev_caret_iterator().
                    dropWhile(info => info.range != range2).
                    dropWhile(info => info.range == range2).
                    find(info => info.info.is_command || info.info.is_begin)
                  match {
                    case Some(Text.Info(range3, tok)) =>
                      if (is_command_kind(tok, Keyword.theory_block)) Some((range1, range3))
                      else Some((range1, range2))
                    case None => None
                  }
                case None => None
              }

            case _ => None
          }
        case None => None
      }
    }

    def getMatch(text_area: TextArea): StructureMatcher.Match =
      find_pair(text_area) match {
        case Some((_, range)) =>
          val line = text_area.getBuffer.getLineOfOffset(range.start)
          new StructureMatcher.Match(Structure_Matching.Isabelle_Matcher,
            line, range.start, line, range.stop)
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

