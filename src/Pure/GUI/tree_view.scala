/*  Title:      Pure/GUI/tree_view.scala
    Author:     Makarius

Tree view with adjusted defaults.
*/

package isabelle

import javax.swing.JTree
import javax.swing.tree.{DefaultMutableTreeNode, DefaultTreeModel, TreeSelectionModel}


class Tree_View(
  val root: DefaultMutableTreeNode = new DefaultMutableTreeNode,
  single_selection_mode: Boolean = false
) extends JTree(root) {
  def get_selection[A](which: PartialFunction[AnyRef, A]): Option[A] =
    getLastSelectedPathComponent match {
      case node: DefaultMutableTreeNode =>
        val obj = node.getUserObject
        if (obj != null && which.isDefinedAt(obj)) Some(which(obj))
        else None
      case _ => None
    }

  def clear(): Unit = {
    clearSelection()
    root.removeAllChildren()
  }

  def reload_model(): Unit =
    getModel.asInstanceOf[DefaultTreeModel].reload(root)


  /* init */

  setRowHeight(0)

  if (single_selection_mode) {
    getSelectionModel.setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)
  }

  // follow jEdit
  if (!GUI.is_macos_laf) {
    putClientProperty("JTree.lineStyle", "Angled")
  }
}
