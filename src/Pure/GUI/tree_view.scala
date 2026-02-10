/*  Title:      Pure/GUI/tree_view.scala
    Author:     Makarius

Tree view with sensible defaults.
*/

package isabelle

import isabelle.graphview.Tree_Panel

import java.awt.event.{KeyEvent, KeyAdapter, MouseEvent, MouseAdapter}
import javax.accessibility.AccessibleContext
import javax.swing.JTree
import javax.swing.tree.{DefaultMutableTreeNode, DefaultTreeCellRenderer, DefaultTreeModel,
  MutableTreeNode, TreePath, TreeSelectionModel}


object Tree_View {
  type Node = DefaultMutableTreeNode

  object Node {
    def apply(obj: AnyRef = null): Node =
      if (obj == null) new DefaultMutableTreeNode else new DefaultMutableTreeNode(obj)

    def unapply(tree_node: MutableTreeNode): Option[AnyRef] =
      tree_node match {
        case node: Node => Some(node.getUserObject)
        case _ => None
      }
  }

  class Cell_Renderer extends DefaultTreeCellRenderer {
    def setup(value: AnyRef): Unit = setIcon(null)

    override def getTreeCellRendererComponent(
      tree: JTree,
      value: AnyRef,
      selected: Boolean,
      expanded: Boolean,
      leaf: Boolean,
      row: Int,
      hasFocus: Boolean
    ): java.awt.Component = {
      super.getTreeCellRendererComponent(tree, value, selected, expanded, leaf, row, hasFocus)
      setup(value)
      this
    }
  }
}

class Tree_View(
  val root: Tree_View.Node = Tree_View.Node(),
  single_selection_mode: Boolean = false,
  accessible_name: String = ""
) extends JTree(root) {

  override def getAccessibleContext: AccessibleContext = {
    if (accessibleContext == null) { accessibleContext = new Accessible_Context }
    accessibleContext
  }
  class Accessible_Context extends AccessibleJTree {
    override def getAccessibleName: String =
      proper_string(accessible_name).getOrElse(proper_string(root.toString).orNull)
  }

  def init_model(body: => Unit): Unit = {
    clearSelection()
    root.removeAllChildren()
    body
    expandRow(0)
    reload_model()
  }

  def reload_model(): Unit =
    getModel match {
      case model: DefaultTreeModel => model.reload(root)
      case _ =>
    }


  /* selection events */

  def handle_selection(path: TreePath): Unit = ()

  def get_selection[A](path: TreePath, which: PartialFunction[AnyRef, A]): Option[A] =
    if (path != null) {
      path.getLastPathComponent match {
        case Tree_View.Node(obj) if obj != null && which.isDefinedAt(obj) => Some(which(obj))
        case _ => None
      }
    }
    else None

  addKeyListener(new KeyAdapter {
    override def keyPressed(e: KeyEvent): Unit = {
      if (!e.isConsumed() && GUI.plain_enter(e)) {
        e.consume()
        handle_selection(getSelectionPath)
      }
    }
  })

  addMouseListener(new MouseAdapter {
    override def mousePressed(e: MouseEvent): Unit =
      if (e.getClickCount == 1) handle_selection(getPathForLocation(e.getX, e.getY))
  })


  /* init */

  if (!isEditable) GUI.suppress_keystrokes(this, k => k.getKeyCode == KeyEvent.VK_F2)

  setCellRenderer(new Tree_View.Cell_Renderer)

  setRowHeight(0)

  if (single_selection_mode) {
    getSelectionModel.setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)
  }

  // follow jEdit
  if (!GUI.is_macos_laf()) {
    putClientProperty("JTree.lineStyle", "Angled")
  }
}
