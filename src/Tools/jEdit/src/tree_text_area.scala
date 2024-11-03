/*  Title:      Tools/jEdit/src/tree_text_area.scala
    Author:     Makarius

GUI component for tree view with pretty-printed text area.
*/

package isabelle.jedit


import isabelle._

import java.awt.Dimension
import java.awt.event.{ComponentEvent, ComponentAdapter, FocusAdapter, FocusEvent,
  MouseEvent, MouseAdapter}
import javax.swing.JComponent
import javax.swing.tree.DefaultMutableTreeNode
import javax.swing.event.TreeSelectionEvent

import scala.swing.{Component, ScrollPane, SplitPane, Orientation}
import scala.swing.event.ButtonClicked

import org.gjt.sp.jedit.View


class Tree_Text_Area(view: View, root_name: String = "Overview") {
  GUI_Thread.require {}


  /* tree view */

  val tree: Tree_View =
    new Tree_View(root = new DefaultMutableTreeNode(root_name), single_selection_mode = true)

  def handle_tree_selection(e: TreeSelectionEvent): Unit = ()
  tree.addTreeSelectionListener((e: TreeSelectionEvent) => handle_tree_selection(e))


  /* text area */

  val pretty_text_area: Pretty_Text_Area = new Pretty_Text_Area(view)

  def handle_resize(): Unit = ()
  def handle_update(): Unit = ()

  lazy val delay_resize: Delay =
    Delay.first(PIDE.session.update_delay, gui = true) { handle_resize() }


  /* main pane */

  val tree_pane: ScrollPane = new ScrollPane(Component.wrap(tree))
  tree_pane.horizontalScrollBarPolicy = ScrollPane.BarPolicy.Always
  tree_pane.verticalScrollBarPolicy = ScrollPane.BarPolicy.Always
  tree_pane.minimumSize = new Dimension(200, 100)

  val main_pane: SplitPane = new SplitPane(Orientation.Vertical) {
    oneTouchExpandable = true
    leftComponent = tree_pane
    rightComponent = Component.wrap(pretty_text_area)
  }


  /* GUI component */

  def handle_focus(): Unit = ()

  def init_gui(parent: JComponent): Unit = {
    parent.addComponentListener(
      new ComponentAdapter {
        override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
        override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
      })
    parent.addFocusListener(
      new FocusAdapter {
        override def focusGained(e: FocusEvent): Unit = handle_focus()
      })

    tree.addMouseListener(
      new MouseAdapter {
        override def mouseClicked(e: MouseEvent): Unit = {
          val click = tree.getPathForLocation(e.getX, e.getY)
          if (click != null && e.getClickCount == 1) handle_focus()
        }
      })

    parent match {
      case dockable: Dockable => dockable.set_content(main_pane)
      case _ =>
    }
  }
}
