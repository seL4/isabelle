/*  Title:      Tools/Graphview/mutator.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Filters and add-operations on graphs.
*/

package isabelle.graphview


import isabelle._

import java.awt.Color
import scala.collection.immutable.SortedSet


object Mutator
{
  sealed case class Info(enabled: Boolean, color: Color, mutator: Mutator)

  def make(graphview: Graphview, m: Mutator): Info =
    Info(true, graphview.Colors.next(), m)

  class Graph_Filter(
    val name: String,
    val description: String,
    pred: Graph_Display.Graph => Graph_Display.Graph) extends Filter
  {
    def filter(graph: Graph_Display.Graph): Graph_Display.Graph = pred(graph)
  }

  class Graph_Mutator(
    val name: String,
    val description: String,
    pred: (Graph_Display.Graph, Graph_Display.Graph) => Graph_Display.Graph) extends Mutator
  {
    def mutate(full_graph: Graph_Display.Graph, graph: Graph_Display.Graph): Graph_Display.Graph =
      pred(full_graph, graph)
  }

  class Node_Filter(
    name: String,
    description: String,
    pred: (Graph_Display.Graph, Graph_Display.Node) => Boolean)
    extends Graph_Filter(name, description, g => g.restrict(pred(g, _)))

  class Edge_Filter(
    name: String,
    description: String,
    pred: (Graph_Display.Graph, Graph_Display.Edge) => Boolean)
    extends Graph_Filter(
      name,
      description,
      g => g.dest.foldLeft(g) {
        case (graph, ((from, _), tos)) =>
          tos.foldLeft(graph) {
            case (gr, to) => if (pred(gr, (from, to))) gr else gr.del_edge(from, to)
          }
      })

  class Node_Family_Filter(
    name: String,
    description: String,
    reverse: Boolean,
    parents: Boolean,
    children: Boolean,
    pred: (Graph_Display.Graph, Graph_Display.Node) => Boolean)
    extends Node_Filter(
      name,
      description,
      (g, k) =>
        reverse !=
          (pred(g, k) ||
            (parents && g.all_preds(List(k)).exists(pred(g, _))) ||
            (children && g.all_succs(List(k)).exists(pred(g, _)))))

  case class Identity()
    extends Graph_Filter(
      "Identity",
      "Does not change the graph.",
      g => g)

  case class Node_Expression(
    regex: String,
    reverse: Boolean,
    parents: Boolean,
    children: Boolean)
    extends Node_Family_Filter(
      "Filter by Name",
      "Only shows or hides all nodes with any family member's name matching a regex.",
      reverse,
      parents,
      children,
      (g, node) => (regex.r findFirstIn node.toString).isDefined)

  case class Node_List(
    list: List[Graph_Display.Node],
    reverse: Boolean,
    parents: Boolean,
    children: Boolean)
    extends Node_Family_Filter(
      "Filter by Name List",
      "Only shows or hides all nodes with any family member's name matching any string in a comma separated list.",
      reverse,
      parents,
      children,
      (g, node) => list.contains(node))

  case class Edge_Endpoints(edge: Graph_Display.Edge)
    extends Edge_Filter(
      "Hide edge",
      "Hides specified edge.",
      (g, e) => e != edge)

  private def add_node_group(from: Graph_Display.Graph, to: Graph_Display.Graph,
    keys: List[Graph_Display.Node]) =
  {
    // Add Nodes
    val with_nodes =
      keys.foldLeft(to) { case (graph, key) => graph.default_node(key, from.get_node(key)) }

    // Add Edges
    keys.foldLeft(with_nodes) {
      case (gv, key) =>
        def add_edges(g: Graph_Display.Graph, keys: from.Keys, succs: Boolean) =
          keys.foldLeft(g) {
            case (graph, end) =>
              if (!graph.keys_iterator.contains(end)) graph
              else {
                if (succs) graph.add_edge(key, end)
                else graph.add_edge(end, key)
              }
          }

        add_edges(
          add_edges(gv, from.imm_preds(key), false),
          from.imm_succs(key), true)
    }
  }

  case class Add_Node_Expression(regex: String)
    extends Graph_Mutator(
      "Add by name",
      "Adds every node whose name matches the regex. " +
      "Adds all relevant edges.",
      (full_graph, graph) =>
        add_node_group(full_graph, graph,
          full_graph.keys.filter(node => (regex.r findFirstIn node.toString).isDefined).toList))

  case class Add_Transitive_Closure(parents: Boolean, children: Boolean)
    extends Graph_Mutator(
      "Add transitive closure",
      "Adds all family members of all current nodes.",
      (full_graph, graph) => {
        val withparents =
          if (parents) add_node_group(full_graph, graph, full_graph.all_preds(graph.keys))
          else graph
        if (children)
          add_node_group(full_graph, withparents, full_graph.all_succs(graph.keys))
        else withparents
      })
}

trait Mutator
{
  val name: String
  val description: String
  def mutate(full_graph: Graph_Display.Graph, graph: Graph_Display.Graph): Graph_Display.Graph

  override def toString: String = name
}

trait Filter extends Mutator
{
  def mutate(full_graph: Graph_Display.Graph, graph: Graph_Display.Graph): Graph_Display.Graph = filter(graph)
  def filter(graph: Graph_Display.Graph): Graph_Display.Graph
}
