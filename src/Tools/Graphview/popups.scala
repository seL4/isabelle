/*  Title:      Tools/Graphview/popups.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

PopupMenu generation for graph components.
*/

package isabelle.graphview


import isabelle._

import javax.swing.JPopupMenu
import scala.swing.{Action, Menu, MenuItem, Separator}


object Popups
{
  def apply(
    graph_panel: Graph_Panel,
    mouse_node: Option[Graph_Display.Node],
    selected_nodes: List[Graph_Display.Node]): JPopupMenu =
  {
    val graphview = graph_panel.graphview

    val add_mutator = graphview.model.Mutators.add _
    val visible_graph = graphview.visible_graph

    def filter_context(
        nodes: List[Graph_Display.Node], reverse: Boolean, caption: String, edges: Boolean) =
      new Menu(caption) {
        contents +=
          new MenuItem(new Action("This") {
            def apply =
              add_mutator(Mutator.make(graphview, Mutator.Node_List(nodes, reverse, false, false)))
          })

        contents +=
          new MenuItem(new Action("Family") {
            def apply =
              add_mutator(Mutator.make(graphview, Mutator.Node_List(nodes, reverse, true, true)))
          })

        contents +=
          new MenuItem(new Action("Parents") {
            def apply =
              add_mutator(Mutator.make(graphview, Mutator.Node_List(nodes, reverse, false, true)))
          })

        contents +=
          new MenuItem(new Action("Children") {
            def apply =
              add_mutator(Mutator.make(graphview, Mutator.Node_List(nodes, reverse, true, false)))
          })

        if (edges) {
          def degree_nodes(succs: Boolean) =
            (for {
              from <- nodes.iterator
              tos = if (succs) visible_graph.imm_succs(from) else visible_graph.imm_preds(from)
              if tos.nonEmpty
            } yield (from, tos)).toList.sortBy(_._1)(Graph_Display.Node.Ordering)

          val outs = degree_nodes(true)
          val ins = degree_nodes(false)

          if (outs.nonEmpty || ins.nonEmpty) {
            contents += new Separator()
            contents +=
              new Menu("Edge") {
                if (outs.nonEmpty) {
                  contents += new MenuItem("From ...") { enabled = false }
                  for ((from, tos) <- outs) {
                    contents +=
                      new Menu(quote(from.toString)) {
                        contents += new MenuItem("To ...") { enabled = false }
                        for (to <- tos) {
                          contents +=
                            new MenuItem(
                              new Action(quote(to.toString)) {
                                def apply =
                                  add_mutator(
                                    Mutator.make(graphview, Mutator.Edge_Endpoints((from, to))))
                              })
                        }
                      }
                  }
                }
                if (outs.nonEmpty && ins.nonEmpty) { contents += new Separator() }
                if (ins.nonEmpty) {
                  contents += new MenuItem("To ...") { enabled = false }
                  for ((to, froms) <- ins) {
                    contents +=
                      new Menu(quote(to.toString)) {
                        contents += new MenuItem("From ...") { enabled = false }
                        for (from <- froms) {
                          contents +=
                            new MenuItem(
                              new Action(quote(from.toString)) {
                                def apply =
                                  add_mutator(
                                    Mutator.make(graphview, Mutator.Edge_Endpoints((from, to))))
                              })
                        }
                      }
                  }
                }
              }
          }
        }
    }

    val popup = new JPopupMenu()

    popup.add(
      new MenuItem(
        new Action("Remove all filters") { def apply = graphview.model.Mutators(Nil) }).peer)
    popup.add(new JPopupMenu.Separator)

    if (mouse_node.isDefined) {
      val node = mouse_node.get
      popup.add(new MenuItem("Mouse over: " + quote(node.toString)) { enabled = false }.peer)

      popup.add(filter_context(List(node), true, "Hide", true).peer)
      popup.add(filter_context(List(node), false, "Show only", false).peer)

      popup.add(new JPopupMenu.Separator)
    }
    if (selected_nodes.nonEmpty) {
      val text =
        if (selected_nodes.length > 1) "multiple"
        else quote(selected_nodes.head.toString)

      popup.add(new MenuItem("Selected: " + text) { enabled = false }.peer)

      popup.add(filter_context(selected_nodes, true, "Hide", true).peer)
      popup.add(filter_context(selected_nodes, false, "Show only", false).peer)
      popup.add(new JPopupMenu.Separator)
    }

    popup.add(new MenuItem(new Action("Fit to window") {
      def apply = graph_panel.fit_to_window() }).peer
    )

    popup
  }
}
