/*  Title:      Tools/jEdit/src/documentation_dockable.scala
    Author:     Makarius

Dockable window for Isabelle documentation.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Dimension, GridLayout}
import javax.swing.{JTree, JScrollPane}
import javax.swing.tree.{DefaultMutableTreeNode, TreeSelectionModel}
import javax.swing.event.{TreeSelectionEvent, TreeSelectionListener}

import org.gjt.sp.jedit.{View, OperatingSystem}


class Documentation_Dockable(view: View, position: String) extends Dockable(view, position)
{
  Swing_Thread.require()

  private val docs = Doc.contents()

  private case class Documentation(name: String, title: String)
  {
    override def toString =
      "<html><b>" + HTML.encode(name) + "</b>:  " + HTML.encode(title) + "</html>"
  }

  private val root = new DefaultMutableTreeNode
  docs foreach {
    case Doc.Section(text) =>
      root.add(new DefaultMutableTreeNode(text))
    case Doc.Doc(name, title) =>
      root.getLastChild.asInstanceOf[DefaultMutableTreeNode]
        .add(new DefaultMutableTreeNode(Documentation(name, title)))
  }

  private val tree = new JTree(root)
  if (!OperatingSystem.isMacOSLF)
    tree.putClientProperty("JTree.lineStyle", "Angled")
  tree.getSelectionModel.setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)
  tree.addTreeSelectionListener(
    new TreeSelectionListener {
      override def valueChanged(e: TreeSelectionEvent)
      {
        tree.getLastSelectedPathComponent match {
          case node: DefaultMutableTreeNode =>
            node.getUserObject match {
              case Documentation(name, _) => Doc.view(name)
              case _ =>
            }
          case _ =>
        }
      }
    })
  tree.setRootVisible(false)
  tree.setVisibleRowCount(docs.length)
  (0 until docs.length).foreach(tree.expandRow)

  private val tree_view = new JScrollPane(tree)
  tree_view.setMinimumSize(new Dimension(100, 50))

  set_content(tree_view)
}
