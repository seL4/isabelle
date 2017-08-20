/*  Title:      Tools/jEdit/src-base/plugin.scala
    Author:     Makarius

Isabelle base environment for jEdit.
*/

package isabelle.jedit_base


import isabelle._

import org.gjt.sp.jedit.EBPlugin


class Plugin extends EBPlugin
{
  override def start()
  {
    Isabelle_System.init()
  }
}
