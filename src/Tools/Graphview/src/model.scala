/*  Title:      Tools/Graphview/src/model.scala
    Author:     Markus Kaiser, TU Muenchen

Internal graph representation.
*/

package isabelle.graphview


import isabelle._
import isabelle.graphview.Mutators._
import java.awt.Color
import scala.actors.Actor
import scala.actors.Actor._


class Mutator_Container(val available: List[Mutator[String, Option[Locale]]]) {
    type Mutator_Markup = (Boolean, Color, Mutator[String, Option[Locale]])
    
    val events = new Event_Bus[Mutator_Event.Message]
    
    private var _mutators : List[Mutator_Markup] = Nil
    def apply() = _mutators
    def apply(mutators: List[Mutator_Markup]){
      _mutators = mutators
      
      events.event(Mutator_Event.NewList(mutators))
    }    

    def add(mutator: Mutator_Markup) = {
      _mutators = _mutators ::: List(mutator)
      
      events.event(Mutator_Event.Add(mutator))
    }
}

class Model(private val graph: Graph[String, Option[Locale]]) {  
  val Mutators = new Mutator_Container(
    List(
      Node_Expression(".*", false, false, false),
      Node_List(Nil, false, false, false),
      Edge_Endpoints("", ""),
      Edge_Transitive(),
      Add_Node_Expression(""),
      Add_Transitive_Closure(true, true)
    ))
  
  val Colors = new Mutator_Container(
    List(
      Node_Expression(".*", false, false, false),
      Node_List(Nil, false, false, false)
    ))  
  
  def visible_nodes(): Iterator[String] = current.keys
  
  def visible_edges(): Iterator[(String, String)] =
    current.keys.map(k => current.imm_succs(k).map((k, _))).flatten
  
  def complete = graph
  def current: Graph[String, Option[Locale]] =
      (graph /: Mutators()) {
        case (g, (enabled, _, mutator)) => {
          if (!enabled) g
          else mutator.mutate(graph, g)
        }
      }
    
  private var _colors = Map[String, Color]()
  def colors = _colors
  
  private def build_colors() {
    (Map[String, Color]() /: Colors()) ({
        case (colors, (enabled, color, mutator)) => {
            (colors /: mutator.mutate(graph, graph).keys) ({
                case (colors, k) => colors + (k -> color)
              })
          }
    })
  }
  Colors.events += actor {
    loop {
      react {
        case _ => build_colors()
      }
    }
  }
}