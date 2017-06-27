/*  Title:      Tools/jEdit/src/protocol_dockable.scala
    Author:     Makarius

Dockable window for protocol messages.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout

import scala.swing.{TextArea, ScrollPane}

import org.gjt.sp.jedit.View


class Protocol_Dockable(view: View, position: String) extends Dockable(view, position)
{
  /* controls */

  private val ml_stats = new Isabelle.ML_Stats

  private val controls = Wrap_Panel(List(ml_stats))


  /* text area */

  private val text_area = new TextArea


  /* layout */

  set_content(new ScrollPane(text_area))
  add(controls.peer, BorderLayout.NORTH)


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case input: Prover.Input =>
        GUI_Thread.later { text_area.append(input.toString + "\n\n") }

      case output: Prover.Output =>
        GUI_Thread.later { text_area.append(output.message.toString + "\n\n") }

      case _: Session.Global_Options =>
        GUI_Thread.later { ml_stats.load() }
    }

  override def init()
  {
    PIDE.session.all_messages += main
    PIDE.session.global_options += main
  }

  override def exit()
  {
    PIDE.session.all_messages -= main
    PIDE.session.global_options -= main
  }
}
