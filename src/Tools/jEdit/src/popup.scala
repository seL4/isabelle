/*  Title:      Tools/jEdit/src/popup.scala
    Author:     Makarius

Popup within layered pane.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Point, Dimension}
import javax.swing.{JLayeredPane, JComponent}


class Popup(
  layered: JLayeredPane,
  component: JComponent,
  location: Point,
  size: Dimension) extends javax.swing.Popup()
{
  override def show
  {
    component.setLocation(location)
    component.setSize(size)
    component.setPreferredSize(size)
    component.setOpaque(true)
    layered.add(component, JLayeredPane.POPUP_LAYER)
    layered.moveToFront(component)
    layered.repaint(component.getBounds())
  }

  override def hide
  {
    val bounds = component.getBounds()
    layered.remove(component)
    layered.repaint(bounds)
  }
}

