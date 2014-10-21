/*  Title:      Tools/jEdit/src/structure_matching.scala
    Author:     Makarius

Structure matcher for Isabelle/Isar outer syntax.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.textarea.{TextArea, StructureMatcher}


object Structure_Matching
{
  object Isabelle_Matcher extends StructureMatcher
  {
    def find_pair(text_area: TextArea): Option[(Text.Range, Text.Range)] =
    {
      val buffer = text_area.getBuffer
      val caret_line = text_area.getCaretLine
      val caret = text_area.getCaretPosition

      PIDE.session.recent_syntax match {
        case syntax: Outer_Syntax if syntax != Outer_Syntax.empty =>
          Token_Markup.line_token_iterator(syntax, buffer, caret_line).
            find({ case (tok, r) => r.touches(caret) })
          match {
            case Some((tok, range1)) if (syntax.command_kind(tok, Keyword.qed_global)) =>
              Token_Markup.line_token_reverse_iterator(syntax, buffer, caret_line).
                dropWhile({ case (_, r) => caret <= r.stop }).
                find({ case (tok, _) => syntax.command_kind(tok, Keyword.theory) })
              match {
                case Some((tok, range2)) if syntax.command_kind(tok, Keyword.theory_goal) =>
                  Some((range1, range2))
                case _ => None
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
          new StructureMatcher.Match(Structure_Matching.Isabelle_Matcher,
            line, range.start, line, range.stop)
        case None => null
      }

    def selectMatch(text_area: TextArea)
    {
      // FIXME
    }
  }
}

