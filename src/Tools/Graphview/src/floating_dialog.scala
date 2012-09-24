/*  Title:      Tools/Graphview/src/floating_dialog.scala
    Author:     Markus Kaiser, TU Muenchen

PopUp Dialog containing node meta-information.
*/

package isabelle.graphview


import isabelle._
import isabelle.jedit.HTML_Panel

import scala.swing.{Dialog, BorderPanel, Component}
import java.awt.{Point, Dimension}


class Floating_Dialog(private val html: String, _title: String, _location: Point)
extends Dialog
{    
  location = _location
  title = _title
  //No adaptive size because we don't want to resize the Dialog about 1 sec
  //after it is shown.
  preferredSize = new Dimension(300, 300)
  peer.setAlwaysOnTop(true)

  private def render_document(text: String) =
    html_panel.peer.render_document("http://localhost", text)

  private val html_panel = new Component()
  {
    override lazy val peer: HTML_Panel =
      new HTML_Panel(Parameters.font_family, Parameters.font_size) with SuperMixin
      {
        setPreferredWidth(290)
      }
  }
  
  render_document(html)
  contents = new BorderPanel {
    add(html_panel, BorderPanel.Position.Center)
  }
}
