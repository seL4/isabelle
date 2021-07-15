/*  Title:      Tools/jEdit/src/base_plugin.scala
    Author:     Makarius

Isabelle base environment for jEdit.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.{EBMessage, Debug, EBPlugin}
import org.gjt.sp.util.SyntaxUtilities


class Base_Plugin extends EBPlugin
{
  override def start(): Unit =
  {
    Isabelle_System.init()

    GUI.use_isabelle_fonts()

    Debug.DISABLE_SEARCH_DIALOG_POOL = true

    Syntax_Style.set_extender(Syntax_Style.Base_Extender)
  }

  override def stop(): Unit =
  {
    Syntax_Style.set_extender(new SyntaxUtilities.StyleExtender)
  }

  override def handleMessage(message: EBMessage): Unit = {}
}
