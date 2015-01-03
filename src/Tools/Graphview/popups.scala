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
    panel: Graph_Panel,
    mouse_node: Option[Graph_Display.Node],
    selected_nodes: List[Graph_Display.Node]): JPopupMenu =
  {
    val visualizer = panel.visualizer

    val add_mutator = visualizer.model.Mutators.add _
    val curr = visualizer.model.current_graph

    def filter_context(
        nodes: List[Graph_Display.Node], reverse: Boolean, caption: String, edges: Boolean) =
      new Menu(caption) {
        contents +=
          new MenuItem(new Action("This") {
            def apply =
              add_mutator(Mutator.make(visualizer, Mutator.Node_List(nodes, reverse, false, false)))
          })

        contents +=
          new MenuItem(new Action("Family") {
            def apply =
              add_mutator(Mutator.make(visualizer, Mutator.Node_List(nodes, reverse, true, true)))
          })

        contents +=
          new MenuItem(new Action("Parents") {
            def apply =
              add_mutator(Mutator.make(visualizer, Mutator.Node_List(nodes, reverse, false, true)))
          })

        contents +=
          new MenuItem(new Action("Children") {
            def apply =
              add_mutator(Mutator.make(visualizer, Mutator.Node_List(nodes, reverse, true, false)))
          })

        if (edges) {
          val outs =
            nodes.map(l => (l, curr.imm_succs(l)))  // FIXME iterator
              .filter(_._2.size > 0).sortBy(_._1)(Graph_Display.Node.Ordering)
          val ins =
            nodes.map(l => (l, curr.imm_preds(l)))  // FIXME iterator
              .filter(_._2.size > 0).sortBy(_._1)(Graph_Display.Node.Ordering)

          if (outs.nonEmpty || ins.nonEmpty) {
            contents += new Separator()

            contents +=
              new Menu("Edge") {
                if (outs.nonEmpty) {
                  contents += new MenuItem("From...") { enabled = false }

                  outs.map(e => {
                    val (from, tos) = e
                    contents +=
                      new Menu(from.toString) {
                        contents += new MenuItem("To...") { enabled = false }

                        tos.toList.sorted(Graph_Display.Node.Ordering).distinct.map(to => {
                          contents +=
                            new MenuItem(
                              new Action(to.toString) {
                                def apply =
                                  add_mutator(
                                    Mutator.make(visualizer, Mutator.Edge_Endpoints((from, to))))
                              })
                        })
                      }
                  })
                }
                if (outs.nonEmpty && ins.nonEmpty) { contents += new Separator() }
                if (ins.nonEmpty) {
                  contents += new MenuItem("To...") { enabled = false }

                  ins.map(e => {
                    val (to, froms) = e
                    contents +=
                      new Menu(to.toString) {
                        contents += new MenuItem("From...") { enabled = false }

                        froms.toList.sorted(Graph_Display.Node.Ordering).distinct.map(from => {
                          contents +=
                            new MenuItem(
                              new Action(from.toString) {
                                def apply =
                                  add_mutator(
                                    Mutator.make(visualizer, Mutator.Edge_Endpoints((from, to))))
                              })
                        })
                      }
                  })
                }
              }
          }
        }
    }

    val popup = new JPopupMenu()

    popup.add(
      new MenuItem(
        new Action("Remove all filters") { def apply = visualizer.model.Mutators(Nil) }).peer)
    popup.add(new JPopupMenu.Separator)

    if (mouse_node.isDefined) {
      val node = mouse_node.get
      popup.add(new MenuItem("Mouseover: " + node) { enabled = false }.peer)

      popup.add(filter_context(List(node), true, "Hide", true).peer)
      popup.add(filter_context(List(node), false, "Show only", false).peer)

      popup.add(new JPopupMenu.Separator)
    }
    if (!selected_nodes.isEmpty) {
      val text =
        if (selected_nodes.length > 1) "Multiple"
        else selected_nodes.head.toString

      popup.add(new MenuItem("Selected: " + text) { enabled = false }.peer)

      popup.add(filter_context(selected_nodes, true, "Hide", true).peer)
      popup.add(filter_context(selected_nodes, false, "Show only", false).peer)
      popup.add(new JPopupMenu.Separator)
    }

    popup.add(
      new MenuItem(new Action("Fit to Window") { def apply = panel.fit_to_window() }).peer)

    popup
  }
}
