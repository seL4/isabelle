/*
 * Dockable window with result message output
 *
 * @author Makarius
 */

package isabelle.jedit


import isabelle.proofdocument.{Command, HTML_Panel}

import scala.actors.Actor._

import javax.swing.JPanel
import java.awt.{BorderLayout, Dimension}

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DockableWindowManager



class Output_Dockable(view: View, position: String) extends JPanel
{
  /* outer panel */

  if (position == DockableWindowManager.FLOATING)
    setPreferredSize(new Dimension(500, 250))

  setLayout(new BorderLayout)


  /* HTML panel */

  private val html_panel = new HTML_Panel(Isabelle.system, Isabelle.Int_Property("font-size"))
  add(html_panel, BorderLayout.CENTER)


  /* actor wiring */

  private val output_actor = actor {
    loop {
      react {
        case cmd: Command =>
          val theory_view = Isabelle.prover_setup(view.getBuffer).get.theory_view
          val body =
            if (cmd == null) Nil  // FIXME ??
            else cmd.results(theory_view.current_document)
          html_panel.render(body)
          
        case bad => System.err.println("output_actor: ignoring bad message " + bad)
      }
    }
  }

  private val properties_actor = actor {
    loop {
      react {
        case _: Unit => html_panel.init(Isabelle.Int_Property("font-size"))
        case bad => System.err.println("properties_actor: ignoring bad message " + bad)
      }
    }
  }

  override def addNotify() {
    super.addNotify()
    Isabelle.plugin.state_update += output_actor
    Isabelle.plugin.properties_changed += properties_actor
  }

  override def removeNotify() {
    Isabelle.plugin.state_update -= output_actor
    Isabelle.plugin.properties_changed -= properties_actor
    super.removeNotify()
  }
}
