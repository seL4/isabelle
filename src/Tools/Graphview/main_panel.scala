/*  Title:      Tools/Graphview/main_panel.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Graph Panel wrapper.
*/

package isabelle.graphview


import isabelle._

import scala.swing.{SplitPane, Orientation}


class Main_Panel(graphview: Graphview) extends SplitPane(Orientation.Vertical)
{
  oneTouchExpandable = true

  val graph_panel = new Graph_Panel(graphview)
  val tree_panel = new Tree_Panel(graphview, graph_panel)

  leftComponent = tree_panel
  rightComponent = graph_panel

  def update_layout(): Unit =
  {
    graphview.update_layout()
    tree_panel.refresh()
    graph_panel.refresh()
  }
  update_layout()
}
