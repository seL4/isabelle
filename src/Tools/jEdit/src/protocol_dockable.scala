/*  Title:      Tools/jEdit/src/protocol_dockable.scala
    Author:     Makarius

Dockable window for protocol messages.
*/

package isabelle.jedit


import isabelle._

import scala.swing.{TextArea, ScrollPane}

import org.gjt.sp.jedit.View


class Protocol_Dockable(view: View, position: String) extends Dockable(view, position)
{
  private val text_area = new TextArea
  set_content(new ScrollPane(text_area))


  /* main */

  private val main =
    Session.Consumer[Prover.Message](getClass.getName) {
      case input: Prover.Input =>
        Swing_Thread.later { text_area.append(input.toString + "\n\n") }

      case output: Prover.Output =>
        Swing_Thread.later { text_area.append(output.message.toString + "\n\n") }
    }

  override def init() { PIDE.session.all_messages += main }
  override def exit() { PIDE.session.all_messages -= main }
}
