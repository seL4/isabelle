/*  Title:      Tools/Graphview/src/floating_dialog.scala
    Author:     Markus Kaiser, TU Muenchen

PopUp Dialog containing node meta-information.
*/

package isabelle.graphview


import isabelle._

import scala.swing.{Dialog, BorderPanel, Component, TextArea}
import java.awt.{Font, Point, Dimension}


class Floating_Dialog(content: XML.Body, _title: String, _location: Point)
extends Dialog
{    
  location = _location
  title = _title
  //No adaptive size because we don't want to resize the Dialog about 1 sec
  //after it is shown.
  preferredSize = new Dimension(300, 300)
  peer.setAlwaysOnTop(true)

  private val text_font = new Font(Parameters.font_family, Font.PLAIN, Parameters.font_size)
  private val text = new TextArea
  text.peer.setFont(text_font)
  text.editable = false

  contents = new BorderPanel { add(text, BorderPanel.Position.Center) }
  text.text = Pretty.string_of(content, 76, Pretty.font_metric(text.peer.getFontMetrics(text_font)))
}
