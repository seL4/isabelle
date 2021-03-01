/*  Title:      Tools/jEdit/src/raw_output_dockable.scala
    Author:     Makarius

Dockable window for raw process output (stdout).
*/

package isabelle.jedit


import isabelle._
import isabelle.jedit_base.Dockable

import scala.swing.{TextArea, ScrollPane}

import org.gjt.sp.jedit.View


class Raw_Output_Dockable(view: View, position: String) extends Dockable(view, position)
{
  private val text_area = new TextArea
  set_content(new ScrollPane(text_area))


  /* main */

  private val main =
    Session.Consumer[Prover.Output](getClass.getName) {
      case output: Prover.Output =>
        GUI_Thread.later {
          text_area.append(XML.content(output.message))
          if (!output.is_stdout && !output.is_stderr) text_area.append("\n")
        }
    }

  override def init(): Unit = { PIDE.session.raw_output_messages += main }
  override def exit(): Unit = { PIDE.session.raw_output_messages -= main }
}
