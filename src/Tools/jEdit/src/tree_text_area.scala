/*  Title:      Tools/jEdit/src/tree_text_area.scala
    Author:     Makarius

GUI component for tree view with pretty-printed text area.
*/

package isabelle.jedit


import isabelle._

import java.awt.{BorderLayout, Dimension}
import java.awt.event.{ComponentEvent, ComponentAdapter, KeyEvent, FocusAdapter, FocusEvent,
  MouseEvent, MouseAdapter}
import javax.swing.{JTree, JMenuItem}
import javax.swing.tree.{DefaultMutableTreeNode, DefaultTreeModel, TreeSelectionModel}
import javax.swing.event.{TreeSelectionEvent, TreeSelectionListener}

import scala.collection.immutable.SortedMap
import scala.swing.{Button, Label, Component, ScrollPane, SplitPane, Orientation, BorderPanel}
import scala.swing.event.ButtonClicked

import org.gjt.sp.jedit.{jEdit, View}
import org.gjt.sp.jedit.menu.EnhancedMenuItem
import org.gjt.sp.jedit.textarea.JEditTextArea


class Tree_Text_Area(view: View, root_name: String = "Overview") {
  GUI_Thread.require {}


  /* tree view */

  val root: DefaultMutableTreeNode = new DefaultMutableTreeNode(root_name)
  val tree: JTree = new JTree(root)

  def get_tree_selection[A](which: PartialFunction[AnyRef, A]): Option[A] =
    tree.getLastSelectedPathComponent match {
      case node: DefaultMutableTreeNode =>
        val obj = node.getUserObject
        if (obj != null && which.isDefinedAt(obj)) Some(which(obj))
        else None
      case _ => None
    }

  def handle_tree_selection(e: TreeSelectionEvent): Unit = ()

  def clear(): Unit = {
    tree.clearSelection()
    root.removeAllChildren()
  }

  def reload(): Unit =
    tree.getModel.asInstanceOf[DefaultTreeModel].reload(root)

  tree.setRowHeight(0)
  tree.getSelectionModel.setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)
  tree.addTreeSelectionListener((e: TreeSelectionEvent) => handle_tree_selection(e))


  /* text area */

  val pretty_text_area: Pretty_Text_Area = new Pretty_Text_Area(view)

  def handle_resize(): Unit = ()
  def handle_update(): Unit = ()

  lazy val delay_resize: Delay =
    Delay.first(PIDE.session.update_delay, gui = true) { handle_resize() }

  lazy val component_resize: ComponentAdapter =
    new ComponentAdapter {
      override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
      override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
    }


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
}
