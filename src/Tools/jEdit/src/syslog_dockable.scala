/*  Title:      Tools/jEdit/src/syslog_dockable.scala
    Author:     Makarius

Dockable window for syslog.
*/

package isabelle.jedit


import isabelle._

import scala.swing.{TextArea, ScrollPane}

import org.gjt.sp.jedit.View


class Syslog_Dockable(view: View, position: String) extends Dockable(view, position)
{
  /* GUI components */

  private val syslog = new TextArea()

  private def syslog_delay = Delay.first(PIDE.options.seconds("editor_update_delay"), gui = true)
  {
    val text = PIDE.session.syslog_content()
    if (text != syslog.text) syslog.text = text
  }

  set_content(new ScrollPane(syslog))


  /* main */

  private val main =
    Session.Consumer[Prover.Output](getClass.getName) { case _ => syslog_delay.invoke() }

  override def init(): Unit =
  {
    PIDE.session.syslog_messages += main
    syslog_delay.invoke()
  }

  override def exit(): Unit =
  {
    PIDE.session.syslog_messages -= main
  }
}
