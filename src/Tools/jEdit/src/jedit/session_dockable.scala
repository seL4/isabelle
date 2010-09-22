/*  Title:      Tools/jEdit/src/jedit/session_dockable.scala
    Author:     Makarius

Dockable window for prover session management.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._
import scala.swing.{TextArea, ScrollPane}

import org.gjt.sp.jedit.View


class Session_Dockable(view: View, position: String) extends Dockable(view: View, position: String)
{
  private val text_area = new TextArea
  text_area.editable = false
  set_content(new ScrollPane(text_area))


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case result: Isabelle_Process.Result =>
          if (result.is_init || result.is_exit || result.is_system)
            Swing_Thread.now { text_area.append(XML.content(result.message).mkString + "\n") }

        case bad => System.err.println("Session_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init() { Isabelle.session.raw_messages += main_actor }
  override def exit() { Isabelle.session.raw_messages -= main_actor }
}
