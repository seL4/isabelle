/*  Title:      Tools/Graphview/src/mutator.scala
    Author:     Markus Kaiser, TU Muenchen

Filters and add-operations on graphs.
*/

package isabelle.graphview


import isabelle._

import java.awt.Color
import scala.collection.immutable.SortedSet


trait Mutator
{
  val name: String
  val description: String
  def mutate(complete: Model.Graph, sub: Model.Graph): Model.Graph

  override def toString() = name
}

trait Filter extends Mutator
{
  def mutate(complete: Model.Graph, sub: Model.Graph) = filter(sub)
  def filter(sub: Model.Graph) : Model.Graph
}

object Mutators {
  type Mutator_Markup = (Boolean, Color, Mutator)
  
  val Enabled = true
  val Disabled = false
  
  def create(m: Mutator): Mutator_Markup =
    (Mutators.Enabled, Parameters.Colors.next, m)

  class Graph_Filter(val name: String, val description: String,
    pred: Model.Graph => Model.Graph)
  extends Filter
  {
    def filter(sub: Model.Graph) : Model.Graph = pred(sub)
  }

  class Graph_Mutator(val name: String, val description: String,
    pred: (Model.Graph, Model.Graph) => Model.Graph)
  extends Mutator
  {
    def mutate(complete: Model.Graph, sub: Model.Graph): Model.Graph =
          pred(complete, sub)
  }

  class Node_Filter(name: String, description: String,
    pred: (Model.Graph, String) => Boolean)
    extends Graph_Filter (

    name,
    description,
    g => g.restrict(pred(g, _))
  )

  class Edge_Filter(name: String, description: String,
    pred: (Model.Graph, String, String) => Boolean)
    extends Graph_Filter (

    name,
    description,
    g => (g /: g.dest) {
      case (graph, ((from, _), tos)) => {
        (graph /: tos) {
          (gr, to) => if (pred(gr, from, to)) gr
                      else gr.del_edge(from, to)
        }
      }
    }
  )

  class Node_Family_Filter(name: String, description: String,
      reverse: Boolean, parents: Boolean, children: Boolean,
      pred: (Model.Graph, String) => Boolean)
    extends Node_Filter(

    name,
    description,
    (g, k) => reverse != (
      pred(g, k) ||
      (parents && g.all_preds(List(k)).exists(pred(g, _))) ||
      (children && g.all_succs(List(k)).exists(pred(g, _)))
    )
  )  
  
  case class Identity()
    extends Graph_Filter(

    "Identity",
    "Does not change the graph.",
    g => g
  )

  case class Node_Expression(regex: String,
    reverse: Boolean, parents: Boolean, children: Boolean)
    extends Node_Family_Filter(

    "Filter by Name",
    "Only shows or hides all nodes with any family member's name matching " +
    "a regex.",
    reverse,
    parents,
    children,
    (g, k) => (regex.r findFirstIn k).isDefined
  )

  case class Node_List(list: List[String],
    reverse: Boolean, parents: Boolean, children: Boolean)
    extends Node_Family_Filter(

    "Filter by Name List",
    "Only shows or hides all nodes with any family member's name matching " +
    "any string in a comma separated list.",
    reverse,
    parents,
    children,
    (g, k) => list.exists(_ == k)
  )

  case class Edge_Endpoints(source: String, dest: String)
    extends Edge_Filter(

    "Hide edge",
    "Hides the edge whose endpoints match strings.",
    (g, s, d) => !(s == source && d == dest)
  )

  case class Edge_Transitive()
    extends Edge_Filter(

    "Hide transitive edges",
    "Hides all transitive edges.",
    (g, s, d) => {
      !g.imm_succs(s).filter(_ != d)  // FIXME iterator
      .exists(p => !(g.irreducible_paths(p, d).isEmpty))
    }
  )

  private def add_node_group(from: Model.Graph, to: Model.Graph,
    keys: List[String]) = {
    
    // Add Nodes
    val with_nodes = 
      (to /: keys) {
        (graph, key) => graph.default_node(key, from.get_node(key))
      }
    
    // Add Edges
    (with_nodes /: keys) {
      (gv, key) => {
        def add_edges(g: Model.Graph, keys: SortedSet[String], succs: Boolean) =
          (g /: keys) {
            (graph, end) => {
              if (!graph.keys.contains(end)) graph
              else {
                if (succs) graph.add_edge(key, end)
                else graph.add_edge(end, key)
              }
            }
          }

        
        add_edges(
          add_edges(gv, from.imm_preds(key), false),
          from.imm_succs(key), true
        )
      }
    }
  }  
  
  case class Add_Node_Expression(regex: String)
    extends Graph_Mutator(

    "Add by name",
    "Adds every node whose name matches the regex. " +
    "Adds all relevant edges.",
    (complete, sub) => {
      add_node_group(complete, sub, complete.keys.filter(
          k => (regex.r findFirstIn k).isDefined
        ).toList)
    }
  )
  
  case class Add_Transitive_Closure(parents: Boolean, children: Boolean)
    extends Graph_Mutator(

    "Add transitive closure",
    "Adds all family members of all current nodes.",
    (complete, sub) => {     
      val withparents = 
        if (parents)
          add_node_group(complete, sub, complete.all_preds(sub.keys.toList))
        else
          sub
      
      if (children)
        add_node_group(complete, withparents,
                       complete.all_succs(sub.keys.toList))
      else 
        withparents
    }
  )
}