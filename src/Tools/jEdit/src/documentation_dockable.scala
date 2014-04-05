/*  Title:      Tools/jEdit/src/documentation_dockable.scala
    Author:     Makarius

Dockable window for Isabelle documentation.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Dimension, GridLayout}
import java.awt.event.{MouseEvent, MouseAdapter}
import javax.swing.{JTree, JScrollPane, JComponent}
import javax.swing.tree.{DefaultMutableTreeNode, TreeSelectionModel}
import javax.swing.event.{TreeSelectionEvent, TreeSelectionListener}

import org.gjt.sp.jedit.{View, OperatingSystem}


class Documentation_Dockable(view: View, position: String) extends Dockable(view, position)
{
  private val docs = Doc.contents()

  private case class Documentation(name: String, title: String, path: Path)
  {
    override def toString =
      "<html><b>" + HTML.encode(name) + "</b>:  " + HTML.encode(title) + "</html>"
  }

  private case class Text_File(name: String, path: Path)
  {
    override def toString = name
  }

  private val root = new DefaultMutableTreeNode
  docs foreach {
    case Doc.Section(text) =>
      root.add(new DefaultMutableTreeNode(text))
    case Doc.Doc(name, title, path) =>
      root.getLastChild.asInstanceOf[DefaultMutableTreeNode]
        .add(new DefaultMutableTreeNode(Documentation(name, title, path)))
    case Doc.Text_File(name: String, path: Path) =>
      root.getLastChild.asInstanceOf[DefaultMutableTreeNode]
        .add(new DefaultMutableTreeNode(Text_File(name, path.expand)))
  }

  private val tree = new JTree(root)

  for (cond <-
    List(JComponent.WHEN_FOCUSED,
      JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT,
      JComponent.WHEN_IN_FOCUSED_WINDOW)) tree.setInputMap(cond, null)

  if (!OperatingSystem.isMacOSLF)
    tree.putClientProperty("JTree.lineStyle", "Angled")
  tree.getSelectionModel.setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)
  tree.addMouseListener(new MouseAdapter {
    override def mouseClicked(e: MouseEvent) {
      val click = tree.getPathForLocation(e.getX, e.getY)
      if (click != null && e.getClickCount == 1) {
        (click.getLastPathComponent, tree.getLastSelectedPathComponent) match {
          case (node: DefaultMutableTreeNode, node1: DefaultMutableTreeNode) if node == node1 =>
            node.getUserObject match {
              case Text_File(_, path) =>
                PIDE.editor.goto_file(view, Isabelle_System.platform_path(path))
              case Documentation(_, _, path) =>
                if (path.is_file)
                  PIDE.editor.goto_file(view, Isabelle_System.platform_path(path))
                else {
                  default_thread_pool.submit(() =>
                    try { Doc.view(path) }
                    catch {
                      case exn: Throwable =>
                        GUI.error_dialog(view,
                          "Documentation error", GUI.scrollable_text(Exn.message(exn)))
                    })
                }
              case _ =>
            }
          case _ =>
        }
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
