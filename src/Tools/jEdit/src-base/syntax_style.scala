/*  Title:      Tools/jEdit/src-base/syntax_style.scala
    Author:     Makarius

Extended syntax styles: dummy version.
*/

package isabelle.jedit_base


import isabelle._

import org.gjt.sp.util.SyntaxUtilities
import org.gjt.sp.jedit.syntax.{Token => JEditToken, SyntaxStyle}


object Syntax_Style
{
  private val plain_range: Int = JEditToken.ID_COUNT
  private val full_range = 6 * plain_range + 1

  object Dummy_Extender extends SyntaxUtilities.StyleExtender
  {
    override def extendStyles(styles: Array[SyntaxStyle]): Array[SyntaxStyle] =
    {
      val new_styles = new Array[SyntaxStyle](full_range)
      for (i <- 0 until full_range) {
        new_styles(i) = styles(i % plain_range)
      }
      new_styles
    }
  }
}
