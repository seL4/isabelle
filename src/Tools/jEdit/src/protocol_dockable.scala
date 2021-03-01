/*  Title:      Tools/jEdit/src/protocol_dockable.scala
    Author:     Makarius

Dockable window for protocol messages.
*/

package isabelle.jedit


import isabelle._
import isabelle.jedit_base.Dockable

import java.awt.BorderLayout

import scala.swing.{TextArea, ScrollPane}

import org.gjt.sp.jedit.View


class Protocol_Dockable(view: View, position: String) extends Dockable(view, position)
{
  /* text area */

  private val text_area = new TextArea


  /* layout */

  set_content(new ScrollPane(text_area))


  /* main */

  private val main =
    Session.Consumer[Prover.Message](getClass.getName) {
      case input: Prover.Input =>
        GUI_Thread.later { text_area.append(input.toString + "\n\n") }

      case output: Prover.Output =>
        GUI_Thread.later { text_area.append(output.message.toString + "\n\n") }
    }

  override def init(): Unit =
  {
    PIDE.session.all_messages += main
  }

  override def exit(): Unit =
  {
    PIDE.session.all_messages -= main
  }
}
