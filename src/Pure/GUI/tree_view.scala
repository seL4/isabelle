/*  Title:      Pure/GUI/tree_view.scala
    Author:     Makarius

Tree view with adjusted defaults.
*/

package isabelle

import javax.swing.JTree
import javax.swing.tree.{MutableTreeNode, TreeSelectionModel}


class Tree_View(root: MutableTreeNode, single_selection_mode: Boolean = false) extends JTree(root) {
  tree =>

  tree.setRowHeight(0)

  if (single_selection_mode) {
    tree.getSelectionModel.setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)
  }

  // follow jEdit
  if (!GUI.is_macos_laf) {
    tree.putClientProperty("JTree.lineStyle", "Angled")
  }
}
