/*  Title:      Tools/Graphview/model.scala
    Author:     Markus Kaiser, TU Muenchen

Internal graph representation.
*/

package isabelle.graphview


import isabelle._
import isabelle.graphview.Mutators._

import java.awt.Color


class Mutator_Container(val available: List[Mutator])
{
  type Mutator_Markup = (Boolean, Color, Mutator)

  val events = new Mutator_Event.Bus

  private var _mutators : List[Mutator_Markup] = Nil
  def apply() = _mutators
  def apply(mutators: List[Mutator_Markup])
  {
    _mutators = mutators
    events.event(Mutator_Event.NewList(mutators))
  }

  def add(mutator: Mutator_Markup)
  {
    _mutators = _mutators ::: List(mutator)
    events.event(Mutator_Event.Add(mutator))
  }
}


object Model
{
  /* node info */

  sealed case class Info(name: String, content: XML.Body)

  val empty_info: Info = Info("", Nil)

  val decode_info: XML.Decode.T[Info] = (body: XML.Body) =>
  {
    import XML.Decode._

    val (name, content) = pair(string, x => x)(body)
    Info(name, content)
  }


  /* graph */

  type Graph = isabelle.Graph[String, Info]

  val decode_graph: XML.Decode.T[Graph] =
    isabelle.Graph.decode(XML.Decode.string, decode_info, converse = true)
}

class Model(private val graph: Model.Graph)
{
  val Mutators = new Mutator_Container(
    List(
      Node_Expression(".*", false, false, false),
      Node_List(Nil, false, false, false),
      Edge_Endpoints("", ""),
      Add_Node_Expression(""),
      Add_Transitive_Closure(true, true)
    ))

  val Colors = new Mutator_Container(
    List(
      Node_Expression(".*", false, false, false),
      Node_List(Nil, false, false, false)
    ))

  def visible_nodes_iterator: Iterator[String] = current.keys_iterator

  def visible_edges_iterator: Iterator[(String, String)] =
    current.keys_iterator.flatMap(k => current.imm_succs(k).iterator.map((k, _)))

  def complete = graph
  def current: Model.Graph =
    (graph /: Mutators()) {
      case (g, (enabled, _, mutator)) => {
        if (!enabled) g
        else mutator.mutate(graph, g)
      }
    }

  private var _colors = Map.empty[String, Color]
  def colors = _colors

  private def build_colors()
  {
    _colors =
      (Map.empty[String, Color] /: Colors()) {
        case (colors, (enabled, color, mutator)) =>
          (colors /: mutator.mutate(graph, graph).keys_iterator) {
            case (colors, k) => colors + (k -> color)
          }
      }
  }
  Colors.events += { case _ => build_colors() }
}
