/*  Title:      Pure/GUI/popup.scala
    Author:     Makarius

Popup within layered pane.
*/

package isabelle


import java.awt.{Point, Dimension}
import javax.swing.{JLayeredPane, JComponent}


abstract class Popup(val root: JLayeredPane, val component: JComponent, point: Point) {
  val screen: GUI.Screen_Location = GUI.screen_location(root, point)

  def size: Dimension

  def show: Unit = {
    component.setLocation(screen.relative(root, size))
    component.setSize(size)
    component.setPreferredSize(size)
    component.setOpaque(true)
    root.add(component, JLayeredPane.POPUP_LAYER)
    root.moveToFront(component)
    root.repaint(component.getBounds())
  }

  def hide: Unit = {
    val bounds = component.getBounds()
    root.remove(component)
    root.repaint(bounds)
  }
}
