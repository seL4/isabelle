/*  Title:      Tools/Graphview/layout.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

DAG layout algorithm, according to:

  Georg Sander, "Graph Layout through the VCG Tool", in: Graph Drawing,
  DIMACS International Workshop (GD'94), Springer LNCS 894, 1995.

  http://dx.doi.org/10.1007/3-540-58950-3_371
  ftp://ftp.cs.uni-sb.de/pub/graphics/vcg/doc/tr-A03-94.ps.gz
*/

package isabelle.graphview


import isabelle._


object Layout
{
  /* graph structure */

  object Vertex
  {
    object Ordering extends scala.math.Ordering[Vertex]
    {
      def compare(v1: Vertex, v2: Vertex): Int =
        (v1, v2) match {
          case (_: Node, _: Dummy) => -1
          case (_: Dummy, _: Node) => 1
          case (Node(a), Node(b)) => Graph_Display.Node.Ordering.compare(a, b)
          case (Dummy(a1, a2, i), Dummy(b1, b2, j)) =>
            Graph_Display.Node.Ordering.compare(a1, b1) match {
              case 0 =>
                Graph_Display.Node.Ordering.compare(a2, b2) match {
                  case 0 => i compare j
                  case ord => ord
                }
              case ord => ord
            }
        }
    }
  }

  sealed abstract class Vertex
  case class Node(node: Graph_Display.Node) extends Vertex
  case class Dummy(node1: Graph_Display.Node, node2: Graph_Display.Node, index: Int) extends Vertex

  object Point { val zero: Point = Point(0.0, 0.0) }
  case class Point(x: Double, y: Double)

  type Graph = isabelle.Graph[Vertex, Point]

  def make_graph(entries: List[((Vertex, Point), List[Vertex])]): Graph =
    isabelle.Graph.make(entries)(Vertex.Ordering)

  val empty_graph: Graph = make_graph(Nil)


  /* layout */

  val empty: Layout = new Layout(Metrics.default, Graph_Display.empty_graph, empty_graph)

  val pendulum_iterations = 10
  val minimize_crossings_iterations = 40


  private type Levels = Map[Vertex, Int]
  private val empty_levels: Levels = Map.empty

  def make(metrics: Metrics, input_graph: Graph_Display.Graph): Layout =
  {
    if (input_graph.is_empty) empty
    else {
      /* initial graph */

      val initial_graph =
        make_graph(
          input_graph.iterator.map(
            { case (a, (_, (_, bs))) => ((Node(a), Point.zero), bs.toList.map(Node(_))) }).toList)

      val initial_levels: Levels =
        (empty_levels /: initial_graph.topological_order) {
          case (levels, vertex) =>
            val level =
              1 + (-1 /: initial_graph.imm_preds(vertex)) { case (m, v) => m max levels(v) }
            levels + (vertex -> level)
        }


      /* graph with dummies */

      val (dummy_graph, dummy_levels) =
        ((initial_graph, initial_levels) /: input_graph.edges_iterator) {
            case ((graph, levels), (node1, node2)) =>
              val v1 = Node(node1); val l1 = levels(v1)
              val v2 = Node(node2); val l2 = levels(v2)
              if (l2 - l1 <= 1) (graph, levels)
              else {
                val dummies_levels =
                  (for { (l, i) <- ((l1 + 1) until l2).iterator.zipWithIndex }
                    yield (Dummy(node1, node2, i), l)).toList
                val dummies = dummies_levels.map(_._1)

                val levels1 = (levels /: dummies_levels)(_ + _)
                val graph1 =
                  ((graph /: dummies)(_.new_node(_, Point.zero)).del_edge(v1, v2) /:
                    (v1 :: dummies ::: List(v2)).sliding(2)) {
                      case (g, List(a, b)) => g.add_edge(a, b) }
                (graph1, levels1)
              }
          }


      /* minimize edge crossings and initial coordinates */

      val levels = minimize_crossings(dummy_graph, level_list(dummy_levels))

      val levels_graph: Graph =
        (((dummy_graph, 0.0) /: levels) {
          case ((graph, y), level) =>
            ((((graph, 0.0) /: level) {
              case ((g, x), v) =>
                val w2 = metrics.box_width2(v)
                (g.map_node(v, _ => Point(x + w2, y)), x + 2 * w2 + metrics.box_gap)
            })._1, y + metrics.box_height(level.length))
        })._1


      /* pendulum layout */

      val output_graph = pendulum(metrics, levels_graph, levels)

      new Layout(metrics, input_graph, output_graph)
    }
  }



  /** edge crossings **/

  private type Level = List[Vertex]

  def minimize_crossings(graph: Graph, levels: List[Level]): List[Level] =
  {
    def resort_level(parent: Level, child: Level, top_down: Boolean): Level =
      child.map(v => {
          val ps = if (top_down) graph.imm_preds(v) else graph.imm_succs(v)
          val weight =
            (0.0 /: ps) { (w, p) => w + (0 max parent.indexOf(p)) } / (ps.size max 1)
          (v, weight)
      }).sortBy(_._2).map(_._1)

    def resort(levels: List[Level], top_down: Boolean) =
      if (top_down)
        (List(levels.head) /: levels.tail)((tops, bot) =>
          resort_level(tops.head, bot, top_down) :: tops).reverse
      else {
        val rev_levels = levels.reverse
        (List(rev_levels.head) /: rev_levels.tail)((bots, top) =>
          resort_level(bots.head, top, top_down) :: bots)
      }

    ((levels, count_crossings(graph, levels), true) /: (1 to minimize_crossings_iterations)) {
      case ((old_levels, old_crossings, top_down), _) => {
          val new_levels = resort(old_levels, top_down)
          val new_crossings = count_crossings(graph, new_levels)
          if (new_crossings < old_crossings)
            (new_levels, new_crossings, !top_down)
          else
            (old_levels, old_crossings, !top_down)
      }
    }._1
  }

  def level_list(levels: Levels): List[Level] =
  {
    val max_lev = (-1 /: levels) { case (m, (_, l)) => m max l }
    val buckets = new Array[Level](max_lev + 1)
    for (l <- 0 to max_lev) { buckets(l) = Nil }
    for ((v, l) <- levels) { buckets(l) = v :: buckets(l) }
    buckets.iterator.map(_.sorted(Vertex.Ordering)).toList
  }

  def count_crossings(graph: Graph, levels: List[Level]): Int =
  {
    def in_level(ls: List[Level]): Int = ls match {
      case List(top, bot) =>
        top.iterator.zipWithIndex.map {
          case (outer_parent, outer_parent_index) =>
            graph.imm_succs(outer_parent).iterator.map(bot.indexOf(_))
            .map(outer_child =>
              (0 until outer_parent_index)
              .map(inner_parent =>
                graph.imm_succs(top(inner_parent)).iterator.map(bot.indexOf(_))
                .filter(inner_child => outer_child < inner_child)
                .size
              ).sum
            ).sum
        }.sum

      case _ => 0
    }

    levels.iterator.sliding(2).map(ls => in_level(ls.toList)).sum
  }



  /** pendulum method **/

  /*This is an auxiliary class which is used by the layout algorithm when
    calculating coordinates with the "pendulum method". A "region" is a
    group of vertices which "stick together".*/
  private class Region(init: Vertex)
  {
    var content: List[Vertex] = List(init)

    def distance(metrics: Metrics, graph: Graph, that: Region): Double =
    {
      val v1 = this.content.last; val x1 = graph.get_node(v1).x + metrics.box_width2(v1)
      val v2 = that.content.head; val x2 = graph.get_node(v2).x - metrics.box_width2(v2)
      x2 - x1 - metrics.box_gap
    }

    def deflection(graph: Graph, top_down: Boolean): Double =
      ((for (a <- content.iterator) yield {
        val x = graph.get_node(a).x
        val bs = if (top_down) graph.imm_preds(a) else graph.imm_succs(a)
        bs.iterator.map(graph.get_node(_).x - x).sum / (bs.size max 1)
      }).sum / content.length).round.toDouble

    def move(graph: Graph, dx: Double): Graph =
      if (dx == 0.0) graph
      else (graph /: content) { case (g, v) => g.map_node(v, p => Point(p.x + dx, p.y)) }
  }

  private type Regions = List[List[Region]]

  def pendulum(metrics: Metrics, levels_graph: Graph, levels: List[Level]): Graph =
  {
    def iteration(graph: Graph, regions: Regions, top_down: Boolean): (Graph, Regions, Boolean) =
    {
      val (graph1, regions1, moved) =
      ((graph, List.empty[List[Region]], false) /: (if (top_down) regions else regions.reverse)) {
        case ((graph, tops, moved), bot) =>
          val bot1 = collapse(graph, bot, top_down)
          val (graph1, moved1) = deflect(graph, bot1, top_down)
          (graph1, bot1 :: tops, moved || moved1)
      }
      (graph1, regions1.reverse, moved)
    }

    def collapse(graph: Graph, level: List[Region], top_down: Boolean): List[Region] =
    {
      if (level.size <= 1) level
      else {
        var next = level
        var regions_changed = true
        while (regions_changed) {
          regions_changed = false
          for (i <- Range(next.length - 1, 0, -1)) {
            val (r1, r2) = (next(i - 1), next(i))
            val d1 = r1.deflection(graph, top_down)
            val d2 = r2.deflection(graph, top_down)

            if (// Do regions touch?
                r1.distance(metrics, graph, r2) <= 0.0 &&
                // Do they influence each other?
                (d1 <= 0.0 && d2 < d1 || d2 > 0.0 && d1 > d2 || d1 > 0.0 && d2 < 0.0))
            {
              regions_changed = true
              r1.content = r1.content ::: r2.content
              next = next.filter(next.indexOf(_) != i)
            }
          }
        }
        next
      }
    }

    def deflect(graph: Graph, level: List[Region], top_down: Boolean): (Graph, Boolean) =
    {
      ((graph, false) /: (0 until level.length)) {
        case ((graph, moved), i) =>
          val r = level(i)
          val d = r.deflection(graph, top_down)
          val offset =
            if (d < 0 && i > 0)
              - (level(i - 1).distance(metrics, graph, r) min (- d))
            else if (d >= 0 && i < level.length - 1)
              r.distance(metrics, graph, level(i + 1)) min d
            else d
          (r.move(graph, offset), moved || d != 0)
      }
    }

    val initial_regions = levels.map(level => level.map(new Region(_)))

    ((levels_graph, initial_regions, true, true) /: (1 to pendulum_iterations)) {
      case ((graph, regions, top_down, moved), _) =>
        if (moved) {
          val (graph1, regions1, moved1) = iteration(graph, regions, top_down)
          (graph1, regions1, !top_down, moved1)
        }
        else (graph, regions, !top_down, moved)
    }._1
  }
}

final class Layout private(
  val metrics: Metrics,
  val input_graph: Graph_Display.Graph,
  val output_graph: Layout.Graph)
{
  /* vertex coordinates */

  def get_vertex(v: Layout.Vertex): Layout.Point =
    if (output_graph.defined(v)) output_graph.get_node(v)
    else Layout.Point.zero

  def translate_vertex(v: Layout.Vertex, dx: Double, dy: Double): Layout =
  {
    if ((dx == 0.0 && dy == 0.0) || !output_graph.defined(v)) this
    else {
      val output_graph1 = output_graph.map_node(v, p => Layout.Point(p.x + dy, p.y + dy))
      new Layout(metrics, input_graph, output_graph1)
    }
  }


  /* dummies */

  def find_dummy(pred: Layout.Point => Boolean): Option[Layout.Dummy] =
    output_graph.iterator.collectFirst({ case (d: Layout.Dummy, (p, _)) if pred(p) => d })

  def dummies_iterator: Iterator[Layout.Point] =
    for ((_: Layout.Dummy, (p, _)) <- output_graph.iterator) yield p

  def dummies_iterator(edge: Graph_Display.Edge): Iterator[Layout.Point] =
    new Iterator[Layout.Point] {
      private var index = 0
      def hasNext: Boolean = output_graph.defined(Layout.Dummy(edge._1, edge._2, index))
      def next: Layout.Point =
      {
        val p = output_graph.get_node(Layout.Dummy(edge._1, edge._2, index))
        index += 1
        p
      }
    }
}

