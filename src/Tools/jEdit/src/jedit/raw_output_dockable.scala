/*  Title:      Tools/jEdit/src/jedit/raw_output_dockable.scala
    Author:     Makarius

Dockable window for raw process output (stdout).
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._
import scala.swing.{TextArea, ScrollPane}

import org.gjt.sp.jedit.View


class Raw_Output_Dockable(view: View, position: String)
  extends Dockable(view: View, position: String)
{
  private val text_area = new TextArea
  text_area.editable = false
  set_content(new ScrollPane(text_area))


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case result: Isabelle_Process.Result =>
          Swing_Thread.now { text_area.append(XML.content(result.message).mkString) }

        case bad => System.err.println("Raw_Output_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init() { Isabelle.session.raw_output += main_actor }
  override def exit() { Isabelle.session.raw_output -= main_actor }
}
