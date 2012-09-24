/*  Title:      Tools/Graphview/src/mutator.scala
    Author:     Markus Kaiser, TU Muenchen

Filters and add-operations on graphs.
*/

package isabelle.graphview


import isabelle._

import java.awt.Color
import scala.collection.immutable.SortedSet


trait Mutator[Key, Entry]
{
  val name: String
  val description: String
  def mutate(complete: Graph[Key, Entry], sub: Graph[Key, Entry]): Graph[Key, Entry]

  override def toString() = name
}

trait Filter[Key, Entry]
extends Mutator[Key, Entry]
{
  def mutate(complete: Graph[Key, Entry], sub: Graph[Key, Entry]) = filter(sub)
  def filter(sub: Graph[Key, Entry]) : Graph[Key, Entry]
}

object Mutators {
  type Key = String
  type Entry = Option[Locale]
  type Mutator_Markup = (Boolean, Color, Mutator[Key, Entry])
  
  val Enabled = true
  val Disabled = false
  
  def create(m: Mutator[Key, Entry]): Mutator_Markup =
    (Mutators.Enabled, Parameters.Colors.next, m)

  class Graph_Filter[Key, Entry](val name: String, val description: String,
    pred: Graph[Key, Entry] => Graph[Key, Entry])
  extends Filter[Key, Entry]
  {
    def filter(sub: Graph[Key, Entry]) : Graph[Key, Entry] = pred(sub)
  }

  class Graph_Mutator[Key, Entry](val name: String, val description: String,
    pred: (Graph[Key, Entry], Graph[Key, Entry]) => Graph[Key, Entry])
  extends Mutator[Key, Entry]
  {
    def mutate(complete: Graph[Key, Entry], sub: Graph[Key, Entry]): Graph[Key, Entry] =
          pred(complete, sub)
  }

  class Node_Filter[Key, Entry](name: String, description: String,
    pred: (Graph[Key, Entry], Key) => Boolean)
    extends Graph_Filter[Key, Entry] (

    name,
    description,
    g => g.restrict(pred(g, _))
  )

  class Edge_Filter[Key, Entry](name: String, description: String,
    pred: (Graph[Key, Entry], Key, Key) => Boolean)
    extends Graph_Filter[Key, Entry] (

    name,
    description,
    g => (g /: g.dest) {
      (graph, k) => {
        val (from, tos) = k
        (graph /: tos) {
          (gr, to) => if (pred(gr, from, to)) gr
                      else gr.del_edge(from, to)
        }
      }
    }
  )

  class Node_Family_Filter[Key, Entry](name: String, description: String,
      reverse: Boolean, parents: Boolean, children: Boolean,
      pred: (Graph[Key, Entry], Key) => Boolean)
    extends Node_Filter[Key, Entry](

    name,
    description,
    (g, k) => reverse != (
      pred(g, k) ||
      (parents && g.all_preds(List(k)).exists(pred(g, _))) ||
      (children && g.all_succs(List(k)).exists(pred(g, _)))
    )
  )  
  
  case class Identity()
    extends Graph_Filter[Key, Entry](

    "Identity",
    "Does not change the graph.",
    g => g
  )

  case class Node_Expression(regex: String,
    reverse: Boolean, parents: Boolean, children: Boolean)
    extends Node_Family_Filter[Key, Entry](

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
    extends Node_Family_Filter[Key, Entry](

    "Filter by Name List",
    "Only shows or hides all nodes with any family member's name matching " +
    "any string in a comma separated list.",
    reverse,
    parents,
    children,
    (g, k) => list.exists(_ == k)
  )

  case class Edge_Endpoints(source: String, dest: String)
    extends Edge_Filter[Key, Entry](

    "Hide edge",
    "Hides the edge whose endpoints match strings.",
    (g, s, d) => !(s == source && d == dest)
  )

  case class Edge_Transitive()
    extends Edge_Filter[Key, Entry](

    "Hide transitive edges",
    "Hides all transitive edges.",
    (g, s, d) => {
      !g.imm_succs(s).filter(_ != d)
      .exists(p => !(g.irreducible_paths(p, d).isEmpty))
    }
  )

  private def add_node_group(from: Graph[Key, Entry], to: Graph[Key, Entry],
    keys: List[Key]) = {
    
    // Add Nodes
    val with_nodes = 
      (to /: keys) {
        (graph, key) => graph.default_node(key, from.get_node(key))
      }
    
    // Add Edges
    (with_nodes /: keys) {
      (gv, key) => {
        def add_edges(g: Graph[Key, Entry], keys: SortedSet[Key], succs: Boolean) =
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
    extends Graph_Mutator[Key, Entry](

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
    extends Graph_Mutator[Key, Entry](

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