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
        case syntax: Outer_Syntax
        if syntax != Outer_Syntax.empty =>

          val limit = PIDE.options.value.int("jedit_structure_limit") max 0

          def iterator(line: Int, lim: Int = limit): Iterator[Text.Info[Token]] =
            Token_Markup.line_token_iterator(syntax, buffer, line, line + lim)

          def rev_iterator(line: Int, lim: Int = limit): Iterator[Text.Info[Token]] =
            Token_Markup.line_token_reverse_iterator(syntax, buffer, line, line - lim)

          iterator(caret_line, 1).find(info => info.range.touches(caret)) match {
            case Some(Text.Info(range1, tok)) if syntax.command_kind(tok, Keyword.qed_global) =>
              rev_iterator(caret_line).dropWhile(info => caret <= info.range.stop).
                find(info => syntax.command_kind(info.info, Keyword.theory))
              match {
                case Some(Text.Info(range2, tok))
                if syntax.command_kind(tok, Keyword.theory_goal) => Some((range1, range2))
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

