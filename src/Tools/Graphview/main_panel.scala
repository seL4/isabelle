/*  Title:      Tools/Graphview/main_panel.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Graph Panel wrapper.
*/

package isabelle.graphview


import isabelle._

import scala.swing.{SplitPane, Orientation}


class Main_Panel(visualizer: Visualizer) extends SplitPane(Orientation.Vertical)
{
  oneTouchExpandable = true

  val graph_panel = new Graph_Panel(visualizer)
  val tree_panel = new Tree_Panel(visualizer, graph_panel)

  leftComponent = tree_panel
  rightComponent = graph_panel

  def update_layout()
  {
    visualizer.update_layout()
    tree_panel.refresh()
    graph_panel.refresh()
  }
  update_layout()
}
