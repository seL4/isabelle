/*  Title:      Tools/Graphview/model.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Internal graph representation.
*/

package isabelle.graphview


import isabelle._

import java.awt.Color


class Mutator_Container(val available: List[Mutator])
{
  val events = new Mutator_Event.Bus

  private var _mutators : List[Mutator.Info] = Nil
  def apply() = _mutators
  def apply(mutators: List[Mutator.Info])
  {
    _mutators = mutators
    events.event(Mutator_Event.New_List(mutators))
  }

  def add(mutator: Mutator.Info)
  {
    _mutators = _mutators ::: List(mutator)
    events.event(Mutator_Event.Add(mutator))
  }
}


class Model(val complete_graph: Graph_Display.Graph)
{
  val Mutators =
    new Mutator_Container(
      List(
        Mutator.Node_Expression(".*", false, false, false),
        Mutator.Node_List(Nil, false, false, false),
        Mutator.Edge_Endpoints((Graph_Display.Node.dummy, Graph_Display.Node.dummy)),
        Mutator.Add_Node_Expression(""),
        Mutator.Add_Transitive_Closure(true, true)))

  val Colors =
    new Mutator_Container(
      List(
        Mutator.Node_Expression(".*", false, false, false),
        Mutator.Node_List(Nil, false, false, false)))

  def find_node(ident: String): Option[Graph_Display.Node] =
    complete_graph.keys_iterator.find(node => node.ident == ident)

  def visible_nodes_iterator: Iterator[Graph_Display.Node] = current_graph.keys_iterator

  def visible_edges_iterator: Iterator[Graph_Display.Edge] =
    current_graph.keys_iterator.flatMap(k => current_graph.imm_succs(k).iterator.map((k, _)))

  def current_graph: Graph_Display.Graph =
    (complete_graph /: Mutators()) {
      case (g, m) => if (!m.enabled) g else m.mutator.mutate(complete_graph, g)
    }

  private var _colors = Map.empty[Graph_Display.Node, Color]
  def colors = _colors

  private def build_colors()
  {
    _colors =
      (Map.empty[Graph_Display.Node, Color] /: Colors()) {
        case (colors, m) =>
          (colors /: m.mutator.mutate(complete_graph, complete_graph).keys_iterator) {
            case (colors, node) => colors + (node -> m.color)
          }
      }
  }
  Colors.events += { case _ => build_colors() }
}
