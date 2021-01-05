/*  Title:      Tools/jEdit/src-base/plugin.scala
    Author:     Makarius

Isabelle base environment for jEdit.
*/

package isabelle.jedit_base


import isabelle._

import org.gjt.sp.jedit.{EBMessage, Debug, EBPlugin}
import org.gjt.sp.util.SyntaxUtilities


class Plugin extends EBPlugin
{
  override def start()
  {
    Isabelle_System.init()

    GUI.set_application_icon()

    Debug.DISABLE_SEARCH_DIALOG_POOL = true

    Syntax_Style.dummy_style_extender()
  }

  override def stop()
  {
    Syntax_Style.set_style_extender(new SyntaxUtilities.StyleExtender)
  }

  override def handleMessage(message: EBMessage) { }
}
