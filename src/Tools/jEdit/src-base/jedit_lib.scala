/*  Title:      Tools/jEdit/src-base/jedit_lib.scala
    Author:     Makarius

Misc library functions for jEdit.
*/

package isabelle.jedit_base


import isabelle._

import org.gjt.sp.jedit.{jEdit, View}


object JEdit_Lib
{
  def request_focus_view(alt_view: View = null): Unit =
  {
    val view = if (alt_view != null) alt_view else jEdit.getActiveView()
    if (view != null) {
      val text_area = view.getTextArea
      if (text_area != null) text_area.requestFocus()
    }
  }
}