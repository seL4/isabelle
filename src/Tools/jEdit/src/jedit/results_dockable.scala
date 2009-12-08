/*
 * Dockable window with result message output
 *
 * @author Makarius
 */

package isabelle.jedit


import isabelle.proofdocument.HTML_Panel

import scala.io.Source
import scala.swing.{BorderPanel, Component}

import java.awt.Dimension

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DockableWindowManager



class Results_Dockable(view: View, position: String) extends BorderPanel
{
  // outer panel

  if (position == DockableWindowManager.FLOATING)
    preferredSize = new Dimension(500, 250)


  // HTML panel

  val html_panel = new HTML_Panel(Isabelle.system, Isabelle.Int_Property("font-size"))
  add(Component.wrap(html_panel), BorderPanel.Position.Center)

  Isabelle.plugin.state_update += (cmd => {
    val theory_view = Isabelle.prover_setup(view.getBuffer).get.theory_view
    val body =
      if (cmd == null) Nil  // FIXME ??
      else cmd.results(theory_view.current_document)
    html_panel.render(body)
  })
}
