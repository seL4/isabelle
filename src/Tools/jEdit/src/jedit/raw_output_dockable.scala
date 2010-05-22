/*  Title:      Tools/jEdit/src/jedit/raw_output_dockable.scala
    Author:     Makarius

Dockable window for raw process output (stdout).
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._

import java.awt.{Dimension, Graphics, BorderLayout}
import javax.swing.{JPanel, JTextArea, JScrollPane}

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DockableWindowManager


class Raw_Output_Dockable(view: View, position: String) extends JPanel(new BorderLayout)
{
  if (position == DockableWindowManager.FLOATING)
    setPreferredSize(new Dimension(500, 250))

  private val text_area = new JTextArea
  add(new JScrollPane(text_area), BorderLayout.CENTER)


  /* actor wiring */

  private val raw_output_actor = actor {
    loop {
      react {
        case result: Isabelle_Process.Result =>
          Swing_Thread.now { text_area.append(XML.content(result.message).mkString) }

        case bad => System.err.println("raw_output_actor: ignoring bad message " + bad)
      }
    }
  }

  override def addNotify()
  {
    super.addNotify()
    Isabelle.session.raw_output += raw_output_actor
  }

  override def removeNotify()
  {
    Isabelle.session.raw_output -= raw_output_actor
    super.removeNotify()
  }
}
