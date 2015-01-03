/*  Title:      Pure/General/graph_display.scala
    Author:     Makarius

Support for graph display.
*/

package isabelle

object Graph_Display
{
  /* graph entries */

  type Entry = ((String, (String, XML.Body)), List[String])


  /* node names */

  object Name
  {
    val dummy: Name = Name("", "")

    object Ordering extends scala.math.Ordering[Name]
    {
      def compare(name1: Name, name2: Name): Int =
        name1.name compare name2.name match {
          case 0 => name1.ident compare name2.ident
          case ord => ord
        }
    }
  }

  sealed case class Name(name: String, ident: String)
  {
    override def toString: String = name
  }


  /* graph structure */

  type Graph = isabelle.Graph[Name, XML.Body]

  val empty_graph: Graph = isabelle.Graph.empty(Name.Ordering)

  def build_graph(entries: List[Entry]): Graph =
  {
    val the_key =
      (Map.empty[String, Name] /: entries) {
        case (m, ((ident, (name, _)), _)) => m + (ident -> Name(name, ident))
      }
    (((empty_graph /: entries) {
        case (g, ((ident, (_, content)), _)) => g.new_node(the_key(ident), content)
      }) /: entries) {
        case (g1, ((ident, _), parents)) =>
          (g1 /: parents) { case (g2, parent) => g2.add_edge(the_key(parent), the_key(ident)) }
      }
  }

  def decode_graph(body: XML.Body): Graph =
  {
    val entries =
    {
      import XML.Decode._
      list(pair(pair(string, pair(string, x => x)), list(string)))(body)
    }
    build_graph(entries)
  }
}

