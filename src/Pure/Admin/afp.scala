/*  Title:      Pure/Admin/afp.scala
    Author:     Makarius

Administrative support for the Archive of Formal Proofs.
*/

package isabelle


object AFP
{
  val repos_source = "https://bitbucket.org/isa-afp/afp-devel"

  def init(options: Options, base_dir: Path = Path.explode("$AFP_BASE")): AFP =
    new AFP(options, base_dir)

  sealed case class Entry(name: String, sessions: List[String])
}

class AFP private(options: Options, val base_dir: Path)
{
  override def toString: String = base_dir.expand.toString

  val main_dir: Path = base_dir + Path.explode("thys")


  /* entries and sessions */

  val entries: List[AFP.Entry] =
    (for (name <- Sessions.parse_roots(main_dir + Sessions.ROOTS)) yield {
      val sessions =
        Sessions.parse_root_entries(main_dir + Path.explode(name) + Sessions.ROOT).map(_.name)
      AFP.Entry(name, sessions)
    }).sortBy(_.name)

  val sessions: List[String] = entries.flatMap(_.sessions)

  val sessions_structure: Sessions.Structure =
    Sessions.load_structure(options, dirs = List(main_dir)).
      selection(Sessions.Selection(sessions = sessions.toList))


  /* dependency graph */

  private def sessions_deps(entry: AFP.Entry): List[String] =
    entry.sessions.flatMap(sessions_structure.imports_graph.imm_preds(_)).distinct.sorted

  lazy val entries_graph: Graph[String, Unit] =
  {
    val session_entries =
      (Map.empty[String, String] /: entries) {
        case (m1, e) => (m1 /: e.sessions) { case (m2, s) => m2 + (s -> e.name) }
      }
    (Graph.empty[String, Unit] /: entries) { case (g, entry) =>
      val e1 = entry.name
      (g.default_node(e1, ()) /: sessions_deps(entry)) { case (g1, s) =>
        (g1 /: session_entries.get(s).filterNot(_ == e1)) { case (g2, e2) =>
          try { g2.default_node(e2, ()).add_edge_acyclic(e2, e1) }
          catch {
            case exn: Graph.Cycles[_] =>
              error(cat_lines(exn.cycles.map(cycle =>
                "Cyclic dependency of " + cycle.map(c => quote(c.toString)).mkString(" via ") +
                " due to session " + quote(s))))
          }
        }
      }
    }
  }

  def entries_graph_display: Graph_Display.Graph =
    Graph_Display.make_graph(entries_graph)

  def entries_json_text: String =
    (for (entry <- entries.iterator) yield {
      val distrib_deps = sessions_deps(entry).filterNot(sessions.contains(_))
      val afp_deps = entries_graph.imm_preds(entry.name).toList
      """
 {""" + JSON.Format(entry.name) + """:
  {"distrib_deps": """ + JSON.Format(distrib_deps) + """,
   "afp_deps": """ + JSON.Format(afp_deps) + """
  }
 }"""
    }).mkString("[", ", ", "\n]\n")


  /* partition sessions */

  val force_partition1: List[String] = List("Category3", "Formula_Derivatives")

  def partition(n: Int): List[String] =
    n match {
      case 0 => Nil
      case 1 | 2 =>
        val graph = sessions_structure.build_graph.restrict(sessions.toSet)
        val force_part1 = graph.all_succs(force_partition1.filter(graph.defined(_))).toSet
        val (isolated_sessions, connected_sessions) =
          graph.keys.partition(a => graph.is_isolated(a) || force_part1.contains(a))
        if (n == 1) isolated_sessions else connected_sessions
      case _ => error("Bad AFP partition: " + n + " (should be 0, 1, 2)")
    }
}
