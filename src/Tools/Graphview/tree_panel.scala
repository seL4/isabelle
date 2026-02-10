/*  Title:      Tools/Graphview/tree_panel.scala
    Author:     Makarius

Tree view on graph nodes.
*/

package isabelle.graphview


import isabelle._

import java.awt.Dimension
import java.awt.event.{KeyEvent, KeyAdapter, MouseEvent, MouseAdapter}
import javax.swing.tree.TreePath
import javax.swing.event.{DocumentListener, DocumentEvent}

import scala.util.matching.Regex
import scala.swing.{Component, ScrollPane, BorderPanel, Label, TextField, Button, Action}


class Tree_Panel(val graphview: Graphview, graph_panel: Graph_Panel)
extends BorderPanel {
  /* main actions */

  private def selection_action(): Unit = {
    if (tree != null) {
      graphview.current_node = None
      graphview.Selection.clear()
      val paths = tree.getSelectionPaths
      if (paths != null) {
        for (path <- paths if path != null) {
          path.getLastPathComponent match {
            case Tree_View.Node(node: Graph_Display.Node) => graphview.Selection.add(node)
            case _ =>
          }
        }
      }
      graph_panel.repaint()
    }
  }

  private def point_action(path: TreePath): Unit = {
    if (tree_pane != null && path != null) {
      val action_node =
        path.getLastPathComponent match {
          case Tree_View.Node(node: Graph_Display.Node) => Some(node)
          case _ => None
        }
      action_node.foreach(graph_panel.scroll_to_node(_))
      graphview.current_node = action_node
      graph_panel.repaint()
    }
  }


  /* tree */

  private var nodes = List.empty[Graph_Display.Node]

  val tree: Tree_View = new Tree_View(root = Tree_View.Node("Nodes"))

  tree.addKeyListener(new KeyAdapter {
    override def keyPressed(e: KeyEvent): Unit =
      if (!e.isConsumed() && GUI.plain_enter(e)) {
        e.consume()
        selection_action()
      }
  })
  tree.addMouseListener(new MouseAdapter {
    override def mousePressed(e: MouseEvent): Unit =
      if (!e.isConsumed() && e.getClickCount == 2) {
        e.consume()
        point_action(tree.getPathForLocation(e.getX, e.getY))
      }
  })

  private val tree_pane = new ScrollPane(Component.wrap(tree))
  tree_pane.horizontalScrollBarPolicy = ScrollPane.BarPolicy.Always
  tree_pane.verticalScrollBarPolicy = ScrollPane.BarPolicy.Always
  tree_pane.minimumSize = new Dimension(200, 100)
  tree_pane.peer.getVerticalScrollBar.setUnitIncrement(10)


  /* controls */

  private var selection_pattern: Option[Regex] = None

  private def selection_filter(node: Graph_Display.Node): Boolean =
    selection_pattern match {
      case None => false
      case Some(re) => re.findFirstIn(node.toString).isDefined
    }

  private val selection_tooltip = "Selection of nodes via regular expression"
  private val selection_field = new TextField(10) { tooltip = selection_tooltip }
  private val selection_field_foreground = selection_field.foreground
  private val selection_label =
    new GUI.Label("Selection:", selection_field) { tooltip = selection_tooltip }

  private val selection_delay =
    Delay.last(graphview.options.seconds("editor_input_delay"), gui = true) {
      val (pattern, ok) =
        selection_field.text match {
          case null | "" => (None, true)
          case s =>
            val pattern = Library.make_regex(s)
            (pattern, pattern.isDefined)
        }
      if (selection_pattern != pattern) {
        selection_pattern = pattern
        tree.setSelectionRows(
          (for { (node, i) <- nodes.iterator.zipWithIndex if selection_filter(node) }
            yield i + 1).toArray)
        tree.repaint()
      }
      selection_field.foreground =
        if (ok) selection_field_foreground else graphview.error_color
    }

  selection_field.peer.getDocument.addDocumentListener(
    new DocumentListener {
      def changedUpdate(e: DocumentEvent): Unit = selection_delay.invoke()
      def insertUpdate(e: DocumentEvent): Unit = selection_delay.invoke()
      def removeUpdate(e: DocumentEvent): Unit = selection_delay.invoke()
    })

  private val selection_apply = new Button {
    action = Action(GUI.Style_HTML.enclose_bold("Apply")) { selection_action () }
    tooltip = "Apply tree selection to graph"
  }

  private val controls =
    Wrap_Panel(List(selection_label, selection_field, selection_apply))


  /* main layout */

  def refresh(): Unit = {
    val new_nodes = graphview.visible_graph.topological_order
    if (nodes != new_nodes) {
      nodes = new_nodes
      tree.init_model { for (node <- nodes) tree.root.add(Tree_View.Node(node)) }
    }
    revalidate()
    repaint()
  }

  layout(tree_pane) = BorderPanel.Position.Center
  layout(controls) = BorderPanel.Position.North
  refresh()
}
