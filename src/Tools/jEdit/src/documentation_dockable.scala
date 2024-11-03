/*  Title:      Tools/jEdit/src/documentation_dockable.scala
    Author:     Makarius

Dockable window for Isabelle documentation.
*/

package isabelle.jedit


import isabelle._

import java.awt.Dimension
import java.awt.event.{KeyEvent, KeyAdapter, MouseEvent, MouseAdapter}
import javax.swing.JScrollPane

import org.gjt.sp.jedit.{View, OperatingSystem}


class Documentation_Dockable(view: View, position: String) extends Dockable(view, position) {
  private val doc_contents = Doc.contents()

  private case class Node(string: String, entry: Doc.Entry) {
    override def toString: String = string
  }

  private val tree = new Tree_View(single_selection_mode = true)

  for (section <- doc_contents.sections) {
    tree.root.add(Tree_View.Node(section.title))
    section.entries.foreach(
      {
        case entry @ Doc.Doc(name, title, _) =>
          val string = "<html><b>" + HTML.output(name) + "</b>:  " + HTML.output(title) + "</html>"
          tree.root.getLastChild.asInstanceOf[Tree_View.Node]
            .add(Tree_View.Node(Node(string, entry)))
        case entry @ Doc.Text_File(name: String, _) =>
          tree.root.getLastChild.asInstanceOf[Tree_View.Node]
            .add(Tree_View.Node(Node(name, entry)))
      })
  }

  override def focusOnDefaultComponent(): Unit = tree.requestFocusInWindow

  private def action(node: Tree_View.Node): Unit = {
    node.getUserObject match {
      case Node(_, Doc.Doc(_, _, path)) =>
        PIDE.editor.goto_doc(view, path)
      case Node(_, Doc.Text_File(_, path)) =>
        PIDE.editor.goto_file(true, view, File.platform_path(path))
      case _ =>
    }
  }

  tree.addKeyListener(new KeyAdapter {
    override def keyPressed(e: KeyEvent): Unit = {
      if (e.getKeyCode == KeyEvent.VK_ENTER) {
        e.consume()
        val path = tree.getSelectionPath
        if (path != null) {
          path.getLastPathComponent match {
            case node: Tree_View.Node => action(node)
            case _ =>
          }
        }
      }
    }
  })
  tree.addMouseListener(new MouseAdapter {
    override def mouseClicked(e: MouseEvent): Unit = {
      val click = tree.getPathForLocation(e.getX, e.getY)
      if (click != null && e.getClickCount == 1) {
        (click.getLastPathComponent, tree.getLastSelectedPathComponent) match {
          case (node: Tree_View.Node, node1: Tree_View.Node) if node == node1 => action(node)
          case _ =>
        }
      }
    }
  })

  {
    var expand = true
    var visible = 0
    var row = 0
    def make_visible(): Unit = { visible += 1; tree.expandRow(row) }
    for (section <- doc_contents.sections) {
      expand = section.important
      make_visible()
      row += 1
      for (_ <- section.entries) {
        if (expand) make_visible()
        row += 1
      }
    }
    tree.setRootVisible(false)
    tree.setVisibleRowCount(visible)
  }

  private val tree_view = new JScrollPane(tree)
  tree_view.setMinimumSize(new Dimension(200, 50))

  set_content(tree_view)
}
