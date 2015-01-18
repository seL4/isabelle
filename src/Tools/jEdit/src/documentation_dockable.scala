/*  Title:      Tools/jEdit/src/documentation_dockable.scala
    Author:     Makarius

Dockable window for Isabelle documentation.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Dimension, GridLayout}
import java.awt.event.{KeyEvent, KeyAdapter, MouseEvent, MouseAdapter}
import javax.swing.{JTree, JScrollPane, JComponent}
import javax.swing.tree.{DefaultMutableTreeNode, TreeSelectionModel}
import javax.swing.event.{TreeSelectionEvent, TreeSelectionListener}

import org.gjt.sp.jedit.{View, OperatingSystem}


class Documentation_Dockable(view: View, position: String) extends Dockable(view, position)
{
  private val docs = Doc.contents()

  private case class Documentation(name: String, title: String, path: Path)
  {
    override def toString: String =
      "<html><b>" + HTML.encode(name) + "</b>:  " + HTML.encode(title) + "</html>"
  }

  private case class Text_File(name: String, path: Path)
  {
    override def toString: String = name
  }

  private val root = new DefaultMutableTreeNode
  docs foreach {
    case Doc.Section(text, _) =>
      root.add(new DefaultMutableTreeNode(text))
    case Doc.Doc(name, title, path) =>
      root.getLastChild.asInstanceOf[DefaultMutableTreeNode]
        .add(new DefaultMutableTreeNode(Documentation(name, title, path)))
    case Doc.Text_File(name: String, path: Path) =>
      root.getLastChild.asInstanceOf[DefaultMutableTreeNode]
        .add(new DefaultMutableTreeNode(Text_File(name, path.expand)))
  }

  private val tree = new JTree(root)

  override def focusOnDefaultComponent { tree.requestFocusInWindow }

  tree.getSelectionModel.setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)

  private def action(node: DefaultMutableTreeNode)
  {
    node.getUserObject match {
      case Text_File(_, path) =>
        PIDE.editor.goto_file(view, Isabelle_System.platform_path(path))
      case Documentation(_, _, path) =>
        if (path.is_file)
          PIDE.editor.goto_file(view, Isabelle_System.platform_path(path))
        else {
          Future.fork {
            try { Doc.view(path) }
            catch {
              case exn: Throwable =>
                GUI.error_dialog(view,
                  "Documentation error", GUI.scrollable_text(Exn.message(exn)))
            }
          }
        }
      case _ =>
    }
  }

  tree.addKeyListener(new KeyAdapter {
    override def keyPressed(e: KeyEvent)
    {
      if (e.getKeyCode == KeyEvent.VK_ENTER) {
        e.consume
        val path = tree.getSelectionPath
        if (path != null) {
          path.getLastPathComponent match {
            case node: DefaultMutableTreeNode => action(node)
            case _ =>
          }
        }
      }
    }
  })
  tree.addMouseListener(new MouseAdapter {
    override def mouseClicked(e: MouseEvent)
    {
      val click = tree.getPathForLocation(e.getX, e.getY)
      if (click != null && e.getClickCount == 1) {
        (click.getLastPathComponent, tree.getLastSelectedPathComponent) match {
          case (node: DefaultMutableTreeNode, node1: DefaultMutableTreeNode) if node == node1 =>
            action(node)
          case _ =>
        }
      }
    }
  })

  {
    var expand = true
    var visible = 0
    def make_visible(row: Int) { visible += 1; tree.expandRow(row) }
    for ((entry, row) <- docs.zipWithIndex) {
      entry match {
        case Doc.Section(_, important) =>
          expand = important
          make_visible(row)
        case _ =>
          if (expand) make_visible(row)
      }
    }
    tree.setRootVisible(false)
    tree.setVisibleRowCount(visible)
  }

  private val tree_view = new JScrollPane(tree)
  tree_view.setMinimumSize(new Dimension(100, 50))

  set_content(tree_view)
}
