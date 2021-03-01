/*  Title:      Pure/Admin/afp.scala
    Author:     Makarius

Administrative support for the Archive of Formal Proofs.
*/

package isabelle


import java.time.LocalDate
import scala.collection.immutable.SortedMap


object AFP
{
  val repos_source = "https://isabelle.sketis.net/repos/afp-devel"

  val groups: Map[String, String] =
    Map("large" -> "full 64-bit memory model or word arithmetic required",
      "slow" -> "CPU time much higher than 60min (on mid-range hardware)",
      "very_slow" -> "elapsed time of many hours (on high-end hardware)")

  val groups_bulky: List[String] = List("large", "slow")

  val chapter: String = "AFP"

  val force_partition1: List[String] = List("Category3", "HOL-ODE")

  def init(options: Options, base_dir: Path = Path.explode("$AFP_BASE")): AFP =
    new AFP(options, base_dir)


  /* entries */

  def parse_date(s: String): Date =
  {
    val t = Date.Formatter.pattern("uuuu-MM-dd").parse(s)
    Date(LocalDate.from(t).atStartOfDay(Date.timezone_berlin))
  }

  def trim_mail(s: String): String = s.replaceAll("<[^>]*>", "").trim

  sealed case class Entry(name: String, metadata: Properties.T, sessions: List[String])
  {
    def get(prop: String): Option[String] = Properties.get(metadata, prop)
    def get_string(prop: String): String = get(prop).getOrElse("")
    def get_strings(prop: String): List[String] =
      space_explode(',', get_string(prop)).map(_.trim).filter(_.nonEmpty)

    def title: String = get_string("title")
    def authors: List[String] = get_strings("author")
    def date: Date =
      parse_date(get("date").getOrElse(error("Missing date for entry " + quote(name))))
    def topics: List[String] = get_strings("topic")
    def `abstract`: String = get_string("abstract").trim
    def maintainers: List[String] = get_strings("notify")
    def contributors: List[String] = get_strings("contributors")
    def license: String = get("license").getOrElse("BSD")

    def rdf_meta_data: Properties.T =
      RDF.meta_data(
        proper_string(title).map(Markup.META_TITLE -> _).toList :::
        authors.map(Markup.META_CREATOR -> _) :::
        contributors.map(Markup.META_CONTRIBUTOR -> _) :::
        List(Markup.META_DATE -> RDF.date_format(date)) :::
        List(Markup.META_LICENSE -> license) :::
        proper_string(`abstract`).map(Markup.META_DESCRIPTION -> _).toList)
  }
}

class AFP private(options: Options, val base_dir: Path)
{
  override def toString: String = base_dir.expand.toString

  val main_dir: Path = base_dir + Path.explode("thys")


  /* metadata */

  private val entry_metadata: Map[String, Properties.T] =
  {
    val metadata_file = base_dir + Path.explode("metadata/metadata")

    var result = Map.empty[String, Properties.T]
    var section = ""
    var props = List.empty[Properties.Entry]

    val Section = """^\[(\S+)\]\s*$""".r
    val Property = """^(\S+)\s*=(.*)$""".r
    val Extra_Line = """^\s+(.*)$""".r
    val Blank_Line = """^\s*$""".r

    def flush(): Unit =
    {
      if (section != "") result += (section -> props.reverse.filter(p => p._2.nonEmpty))
      section = ""
      props = Nil
    }

    for ((line, i) <- split_lines(File.read(metadata_file)).zipWithIndex)
    {
      def err(msg: String): Nothing =
        error(msg + Position.here(Position.Line_File(i + 1, metadata_file.expand.implode)))

      line match {
        case Section(name) => flush(); section = name
        case Property(a, b) =>
          if (section == "") err("Property without a section")
          props = (a -> b.trim) :: props
        case Extra_Line(line) =>
          props match {
            case Nil => err("Extra line without a property")
            case (a, b) :: rest => props = (a, b + "\n" + line.trim) :: rest
          }
        case Blank_Line() =>
        case _ => err("Bad input")
      }
    }

    flush()
    result
  }


  /* entries */

  val entries_map: SortedMap[String, AFP.Entry] =
  {
    val entries =
      for (name <- Sessions.parse_roots(main_dir + Sessions.ROOTS)) yield {
        val metadata =
          entry_metadata.getOrElse(name, error("Entry without metadata: " + quote(name)))
        val sessions =
          Sessions.parse_root_entries(main_dir + Path.explode(name) + Sessions.ROOT).map(_.name)
        AFP.Entry(name, metadata, sessions)
      }

    val entries_map =
      (SortedMap.empty[String, AFP.Entry] /: entries)({ case (m, e) => m + (e.name -> e) })

    val extra_metadata =
      (for ((name, _) <- entry_metadata.iterator if !entries_map.isDefinedAt(name)) yield name).
        toList.sorted
    if (extra_metadata.nonEmpty)
      error("Meta data without entry: " + commas_quote(extra_metadata))

    entries_map
  }

  val entries: List[AFP.Entry] = entries_map.toList.map(_._2)


  /* sessions */

  val sessions_map: SortedMap[String, AFP.Entry] =
    (SortedMap.empty[String, AFP.Entry] /: entries)(
      { case (m1, e) => (m1 /: e.sessions)({ case (m2, s) => m2 + (s -> e) }) })

  val sessions: List[String] = entries.flatMap(_.sessions)

  val sessions_structure: Sessions.Structure =
    Sessions.load_structure(options, dirs = List(main_dir)).
      selection(Sessions.Selection(sessions = sessions.toList))


  /* dependency graph */

  private def sessions_deps(entry: AFP.Entry): List[String] =
    entry.sessions.flatMap(sessions_structure.imports_graph.imm_preds).distinct.sorted

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

  def partition(n: Int): List[String] =
    n match {
      case 0 => Nil
      case 1 | 2 =>
        val graph = sessions_structure.build_graph.restrict(sessions.toSet)
        val force_part1 =
          graph.all_preds(graph.all_succs(AFP.force_partition1.filter(graph.defined))).toSet
        val (part1, part2) = graph.keys.partition(a => force_part1(a) || graph.is_isolated(a))
        if (n == 1) part1 else part2
      case _ => error("Bad AFP partition: " + n + " (should be 0, 1, 2)")
    }
}
