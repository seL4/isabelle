/*  Title:      Pure/General/graph_display.scala
    Author:     Makarius

Support for graph display.
*/

package isabelle

object Graph_Display
{
  /* graph entries */

  type Entry = ((String, (String, XML.Body)), List[String])  // ident, name, content, parents


  /* graph structure */

  object Node
  {
    val dummy: Node = Node("", "")

    object Ordering extends scala.math.Ordering[Node]
    {
      def compare(node1: Node, node2: Node): Int =
        node1.name compare node2.name match {
          case 0 => node1.ident compare node2.ident
          case ord => ord
        }
    }
  }
  sealed case class Node(name: String, ident: String)
  {
    def is_dummy: Boolean = this == Node.dummy
    override def toString: String = name
  }

  type Edge = (Node, Node)

  type Graph = isabelle.Graph[Node, XML.Body]

  val empty_graph: Graph = isabelle.Graph.empty(Node.Ordering)

  def build_graph(entries: List[Entry]): Graph =
  {
    val node =
      entries.foldLeft(Map.empty[String, Node]) {
        case (m, ((ident, (name, _)), _)) => m + (ident -> Node(name, ident))
      }
    entries.foldLeft(
      entries.foldLeft(empty_graph) {
        case (g, ((ident, (_, content)), _)) => g.new_node(node(ident), content)
      }) {
        case (g1, ((ident, _), parents)) =>
          parents.foldLeft(g1) { case (g2, parent) => g2.add_edge(node(parent), node(ident)) }
      }
  }

  def decode_graph(body: XML.Body): Graph =
    build_graph(
      {
        import XML.Decode._
        list(pair(pair(string, pair(string, x => x)), list(string)))(body)
      })

  def make_graph[A](
    graph: isabelle.Graph[String, A],
    isolated: Boolean = false,
    name: (String, A) => String = (x: String, a: A) => x): Graph =
  {
    val entries =
      (for { (x, (a, (ps, _))) <- graph.iterator if isolated || !graph.is_isolated(x) }
       yield ((x, (name(x, a), Nil)), ps.toList)).toList
    build_graph(entries)
  }
}
