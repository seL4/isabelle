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
    def getMatch(text_area: TextArea): StructureMatcher.Match =
    {
      val buffer = text_area.getBuffer
      val caret_line = text_area.getCaretLine

      PIDE.session.recent_syntax match {
        case syntax: Outer_Syntax if syntax != Outer_Syntax.empty =>
          Token_Markup.buffer_line_tokens(syntax, buffer, caret_line) match {
            case Some(tokens) =>
              // FIXME
              null
            case None => null
          }
        case _ => null
      }
    }

    def selectMatch(text_area: TextArea)
    {
      // FIXME
    }
  }
}

