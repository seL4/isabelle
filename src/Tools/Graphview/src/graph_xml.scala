/*  Title:      Tools/Graphview/src/graph_xml.scala
    Author:     Markus Kaiser, TU Muenchen

XML to graph conversion.
*/

package isabelle.graphview


import isabelle._


case class Locale(val axioms: List[XML.Body], val parameters: List[(String, XML.Body)])

object Graph_XML
{
  type Entry = Option[Locale]
  type Nodes = List[(String, (Entry, List[String]))]
  
  def apply(xml: XML.Tree): Graph[String, Entry] = {
    val nodes : Nodes =
    {
      try {
        xml match {
          case XML.Elem(Markup("thy_deps", Nil), ts) => thy_deps(ts)
          case XML.Elem(Markup("locale_deps", Nil), ts) => locale_deps(ts)
          case _ => Nil
        }
      }
    }

    // Add nodes
    val node_graph =
      (Graph.string[Entry] /: nodes) {
        case (graph, (key, (info, _))) => graph.new_node(key, info)
      }
    
    // Add edges
    (node_graph /: nodes) {
      case (graph, (from, (_, tos))) =>
        (graph /: tos) {
          (graph, to) => graph.add_edge(from, to)
        }
    }
  }

  private def thy_deps(ts: XML.Body) : Nodes = {
    val strings : List[(String, List[String])] = {
      import XML.Decode._
      
      list(pair(string, list(string)))(ts)
    }

    strings.map({case (key, tos) => (key, (None, tos))})
  }

  private def locale_deps(ts: XML.Body) : Nodes = {
    // Identity functions return (potential) term-xmls
    val strings = {
      import XML.Decode._
      val node = pair(list(x=>x),pair(list(pair(string,x=>x)),list(list(x=>x))))
      val graph = list(pair(pair(string, node), list(string)))
      def symtab[A](f: T[A]) = list(pair(x=>x, f))
      val dependencies = symtab(symtab(list(list(x=>x))))
      pair(graph, dependencies)(ts)
    }

    strings._1.map({
        case ((key, (axioms, (parameters, _))), tos) =>
          (key, (Some(Locale(axioms, parameters)), tos))
      }
    )
  }
}
