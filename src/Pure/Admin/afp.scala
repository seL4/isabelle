/*  Title:      Pure/Admin/afp.scala
    Author:     Makarius

Administrative support for the Archive of Formal Proofs.
*/

package isabelle


object AFP
{
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

  val sessions_structure: Sessions.T =
    Sessions.load(options, dirs = List(main_dir)).
      selection(Sessions.Selection(sessions = sessions.toList))._2


  /* dependency graph */

  private def sessions_deps(entry: AFP.Entry): List[String] =
    entry.sessions.flatMap(sessions_structure.imports_graph.imm_preds(_)).distinct.sorted

  val entries_graph: Graph[String, Unit] =
  {
    val session_entries =
      (Multi_Map.empty[String, String] /: entries) { case (m1, e) =>
        (m1 /: e.sessions) { case (m2, s) => m2.insert(s, e.name) }
      }
    (Graph.empty[String, Unit] /: entries) { case (g, e1) =>
      val name1 = e1.name
      val g1 = g.default_node(name1, ())
      (g1 /: sessions_deps(e1)) { case (g2, s2) =>
        (g2 /: session_entries.get_list(s2)) { case (g3, name2) =>
          if (name1 == name2) g3 else g3.default_node(name2, ()).add_edge(name2, name1)
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
}
