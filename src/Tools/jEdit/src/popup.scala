/*  Title:      Tools/jEdit/src/popup.scala
    Author:     Makarius

Simple popup within layered pane, based on component with given geometry.
*/

package isabelle.jedit


import isabelle._

import javax.swing.{JLayeredPane, JComponent}


class Popup(
  layered: JLayeredPane,
  component: JComponent) extends javax.swing.Popup()
{
  override def show
  {
    component.setOpaque(true)
    layered.add(component, JLayeredPane.POPUP_LAYER)
    layered.repaint(component.getBounds())
  }

  override def hide
  {
    val bounds = component.getBounds()
    layered.remove(component)
    layered.repaint(bounds)
  }
}

