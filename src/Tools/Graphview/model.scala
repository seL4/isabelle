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
  def apply(): List[Mutator.Info] = _mutators
  def apply(mutators: List[Mutator.Info]): Unit =
  {
    _mutators = mutators
    events.event(Mutator_Event.New_List(mutators))
  }

  def add(mutator: Mutator.Info): Unit =
  {
    _mutators = _mutators ::: List(mutator)
    events.event(Mutator_Event.Add(mutator))
  }
}


class Model(val full_graph: Graph_Display.Graph)
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
    full_graph.keys_iterator.find(node => node.ident == ident)

  def make_visible_graph(): Graph_Display.Graph =
    (full_graph /: Mutators()) {
      case (g, m) => if (!m.enabled) g else m.mutator.mutate(full_graph, g)
    }

  private var _colors = Map.empty[Graph_Display.Node, Color]
  def colors = _colors

  private def build_colors(): Unit =
  {
    _colors =
      (Map.empty[Graph_Display.Node, Color] /: Colors()) {
        case (colors, m) =>
          (colors /: m.mutator.mutate(full_graph, full_graph).keys_iterator) {
            case (colors, node) => colors + (node -> m.color)
          }
      }
  }
  Colors.events += { case _ => build_colors() }
}
