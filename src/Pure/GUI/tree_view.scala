/*  Title:      Pure/GUI/tree_view.scala
    Author:     Makarius

Tree view with sensible defaults.
*/

package isabelle

import javax.swing.JTree
import javax.swing.tree.{MutableTreeNode, DefaultMutableTreeNode, DefaultTreeModel,
  TreeSelectionModel}


object Tree_View {
  type Node = DefaultMutableTreeNode

  object Node {
    def apply(obj: AnyRef = null): Node =
      if (obj == null) new DefaultMutableTreeNode else new DefaultMutableTreeNode(obj)

    def unapply(tree_node: MutableTreeNode): Option[AnyRef] =
      tree_node match {
        case node: Node if node.getUserObject != null => Some(node.getUserObject)
        case _ => None
      }
  }
}

class Tree_View(
  val root: Tree_View.Node = Tree_View.Node(),
  single_selection_mode: Boolean = false
) extends JTree(root) {
  def get_selection[A](which: PartialFunction[AnyRef, A]): Option[A] =
    getLastSelectedPathComponent match {
      case Tree_View.Node(obj) if which.isDefinedAt(obj) => Some(which(obj))
      case _ => None
    }

  def clear(): Unit = {
    clearSelection()
    root.removeAllChildren()
  }

  def reload_model(): Unit =
    getModel match {
      case model: DefaultTreeModel => model.reload(root)
      case _ =>
    }


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
