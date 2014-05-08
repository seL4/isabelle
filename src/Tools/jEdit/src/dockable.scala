/*  Title:      Tools/jEdit/src/dockable.scala
    Author:     Makarius

Generic dockable window.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Dimension, Component, BorderLayout}
import javax.swing.JPanel

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.{DefaultFocusComponent, DockableWindowManager}


class Dockable(view: View, position: String)
  extends JPanel(new BorderLayout) with DefaultFocusComponent
{
  if (position == DockableWindowManager.FLOATING)
    setPreferredSize(new Dimension(500, 250))

  def focusOnDefaultComponent { requestFocus }

  def set_content(c: Component) { add(c, BorderLayout.CENTER) }
  def set_content(c: scala.swing.Component) { add(c.peer, BorderLayout.CENTER) }

  def detach_operation: Option[() => Unit] = None

  protected def init() { }
  protected def exit() { }

  override def addNotify()
  {
    super.addNotify()
    init()
  }

  override def removeNotify()
  {
    exit()
    super.removeNotify()
  }
}
