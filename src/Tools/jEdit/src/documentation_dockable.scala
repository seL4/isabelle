/*  Title:      Tools/jEdit/src/documentation_dockable.scala
    Author:     Makarius

Dockable window for Isabelle documentation.
*/

package isabelle.jedit


import isabelle._

import java.awt.Dimension
import javax.swing.JScrollPane
import javax.swing.tree.TreePath

import org.gjt.sp.jedit.View


class Documentation_Dockable(view: View, position: String) extends Dockable(view, position) {
  private val doc_contents = Doc.contents(PIDE.ml_settings)

  private val tree =
    new Tree_View(single_selection_mode = true, accessible_name = "Documentation") {
      override def handle_selection(path: TreePath): Unit =
        for (entry <- get_selection(path, { case x: Doc.Entry => x })) {
          PIDE.editor.goto_doc(view, entry.path, focus = true)
        }
    }

  for (section <- doc_contents.sections) {
    tree.root.add(Tree_View.Node(section.title))
    val last_node = tree.root.getLastChild.asInstanceOf[Tree_View.Node]
    for (entry <- section.entries) last_node.add(Tree_View.Node(entry))
  }

  override def focusOnDefaultComponent(): Unit = tree.requestFocusInWindow

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

  private val tree_scroller = new JScrollPane(tree)
  tree_scroller.setMinimumSize(new Dimension(200, 50))

  set_content(tree_scroller)
}
