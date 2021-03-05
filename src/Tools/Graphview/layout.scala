/*  Title:      Tools/Graphview/layout.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

DAG layout according to:

  Georg Sander, "Graph Layout through the VCG Tool", in: Graph Drawing,
  DIMACS International Workshop (GD'94), Springer LNCS 894, 1995.

  https://doi.org/10.1007/3-540-58950-3_371
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
          case (Node(a), Dummy(b, _, _)) =>
            Graph_Display.Node.Ordering.compare(a, b) match {
              case 0 => -1
              case ord => ord
            }
          case (Dummy(a, _, _), Node(b)) =>
            Graph_Display.Node.Ordering.compare(a, b) match {
              case 0 => 1
              case ord => ord
            }
        }
    }
  }

  sealed abstract class Vertex
  case class Node(node: Graph_Display.Node) extends Vertex
  case class Dummy(node1: Graph_Display.Node, node2: Graph_Display.Node, index: Int) extends Vertex

  sealed case class Info(
    x: Double, y: Double, width2: Double, height2: Double, lines: List[String])
  {
    def left: Double = x - width2
    def right: Double = x + width2
    def width: Double = 2 * width2
    def height: Double = 2 * height2
  }

  type Graph = isabelle.Graph[Vertex, Info]

  def make_graph(entries: List[((Vertex, Info), List[Vertex])]): Graph =
    isabelle.Graph.make(entries)(Vertex.Ordering)

  val empty_graph: Graph = make_graph(Nil)


  /* vertex x coordinate */

  private def vertex_left(graph: Graph, v: Vertex) = graph.get_node(v).left
  private def vertex_right(graph: Graph, v: Vertex) = graph.get_node(v).right

  private def move_vertex(graph: Graph, v: Vertex, dx: Double): Graph =
    if (dx == 0.0) graph else graph.map_node(v, info => info.copy(x = info.x + dx))


  /* layout */

  val empty: Layout = new Layout(Metrics.default, Graph_Display.empty_graph, empty_graph)


  private type Levels = Map[Vertex, Int]
  private val empty_levels: Levels = Map.empty

  def make(options: Options, metrics: Metrics,
    node_text: (Graph_Display.Node, XML.Body) => String,
    input_graph: Graph_Display.Graph): Layout =
  {
    if (input_graph.is_empty) empty
    else {
      /* initial graph */

      val initial_graph =
        make_graph(
          input_graph.iterator.map(
            { case (a, (content, (_, bs))) =>
                val lines = split_lines(node_text(a, content))
                val w2 = metrics.node_width2(lines)
                val h2 = metrics.node_height2(lines.length)
                ((Node(a), Info(0.0, 0.0, w2, h2, lines)), bs.toList.map(Node))
            }).toList)

      val initial_levels: Levels =
        initial_graph.topological_order.foldLeft(empty_levels) {
          case (levels, vertex) =>
            val level =
              1 + initial_graph.imm_preds(vertex).foldLeft(-1) { case (m, v) => m max levels(v) }
            levels + (vertex -> level)
        }


      /* graph with dummies */

      val dummy_info = Info(0.0, 0.0, metrics.dummy_size2, metrics.dummy_size2, Nil)

      val (dummy_graph, dummy_levels) =
        input_graph.edges_iterator.foldLeft((initial_graph, initial_levels)) {
          case ((graph, levels), (node1, node2)) =>
            val v1 = Node(node1); val l1 = levels(v1)
            val v2 = Node(node2); val l2 = levels(v2)
            if (l2 - l1 <= 1) (graph, levels)
            else {
              val dummies_levels =
                (for { (l, i) <- ((l1 + 1) until l2).iterator.zipWithIndex }
                  yield (Dummy(node1, node2, i), l)).toList
              val dummies = dummies_levels.map(_._1)

              val levels1 = dummies_levels.foldLeft(levels)(_ + _)
              val graph1 =
                (v1 :: dummies ::: List(v2)).sliding(2).
                  foldLeft(dummies.foldLeft(graph)(_.new_node(_, dummy_info)).del_edge(v1, v2)) {
                    case (g, List(a, b)) => g.add_edge(a, b)
                  }
              (graph1, levels1)
            }
        }


      /* minimize edge crossings and initial coordinates */

      val levels = minimize_crossings(options, dummy_graph, level_list(dummy_levels))

      val levels_graph: Graph =
        levels.foldLeft((dummy_graph, 0.0)) {
          case ((graph, y), level) =>
            val num_lines = level.foldLeft(0) { case (n, v) => n max graph.get_node(v).lines.length }
            val num_edges = level.foldLeft(0) { case (n, v) => n + graph.imm_succs(v).size }

            val y1 = y + metrics.node_height2(num_lines)

            val graph1 =
              level.foldLeft((graph, 0.0)) {
                case ((g, x), v) =>
                  val info = g.get_node(v)
                  val g1 = g.map_node(v, _ => info.copy(x = x + info.width2, y = y1))
                  val x1 = x + info.width + metrics.gap
                  (g1, x1)
              }._1

            val y2 = y1 + metrics.level_height2(num_lines, num_edges)

            (graph1, y2)
        }._1


      /* pendulum/rubberband layout */

      val output_graph =
        rubberband(options, metrics, levels,
          pendulum(options, metrics, levels, levels_graph))

      new Layout(metrics, input_graph, output_graph)
    }
  }



  /** edge crossings **/

  private type Level = List[Vertex]

  private def minimize_crossings(
    options: Options, graph: Graph, levels: List[Level]): List[Level] =
  {
    def resort(parent: Level, child: Level, top_down: Boolean): Level =
      child.map(v =>
      {
        val ps = if (top_down) graph.imm_preds(v) else graph.imm_succs(v)
        val weight =
          ps.foldLeft(0.0) { case (w, p) => w + (0 max parent.indexOf(p)) } / (ps.size max 1)
        (v, weight)
      }).sortBy(_._2).map(_._1)

    (1 to (2 * options.int("graphview_iterations_minimize_crossings"))).
      foldLeft((levels, count_crossings(graph, levels))) {
        case ((old_levels, old_crossings), iteration) =>
          val top_down = (iteration % 2 == 1)
          val new_levels =
            if (top_down) {
              old_levels.tail.foldLeft(List(old_levels.head)) {
                case (tops, bot) => resort(tops.head, bot, top_down) :: tops
              }.reverse
            }
            else {
              val rev_old_levels = old_levels.reverse
              rev_old_levels.tail.foldLeft(List(rev_old_levels.head)) {
                case (bots, top) => resort(bots.head, top, top_down) :: bots
              }
            }
          val new_crossings = count_crossings(graph, new_levels)
          if (new_crossings < old_crossings)
            (new_levels, new_crossings)
          else
            (old_levels, old_crossings)
      }._1
  }

  private def level_list(levels: Levels): List[Level] =
  {
    val max_lev = levels.foldLeft(-1) { case (m, (_, l)) => m max l }
    val buckets = new Array[Level](max_lev + 1)
    for (l <- 0 to max_lev) { buckets(l) = Nil }
    for ((v, l) <- levels) { buckets(l) = v :: buckets(l) }
    buckets.iterator.map(_.sorted(Vertex.Ordering)).toList
  }

  private def count_crossings(graph: Graph, levels: List[Level]): Int =
    levels.iterator.sliding(2).map {
      case List(top, bot) =>
        top.iterator.zipWithIndex.map {
          case (outer_parent, outer_parent_index) =>
            graph.imm_succs(outer_parent).iterator.map(bot.indexOf(_)).map(outer_child =>
              (0 until outer_parent_index).iterator.map(inner_parent =>
                graph.imm_succs(top(inner_parent)).iterator.map(bot.indexOf(_))
                  .count(inner_child => outer_child < inner_child)).sum).sum
        }.sum
      case _ => 0
    }.sum



  /** pendulum method **/

  /*This is an auxiliary class which is used by the layout algorithm when
    calculating coordinates with the "pendulum method". A "region" is a
    group of vertices which "stick together".*/
  private class Region(val content: List[Vertex])
  {
    def distance(metrics: Metrics, graph: Graph, that: Region): Double =
      vertex_left(graph, that.content.head) -
      vertex_right(graph, this.content.last) -
      metrics.gap

    def deflection(graph: Graph, top_down: Boolean): Double =
      ((for (a <- content.iterator) yield {
        val x = graph.get_node(a).x
        val bs = if (top_down) graph.imm_preds(a) else graph.imm_succs(a)
        bs.iterator.map(graph.get_node(_).x - x).sum / (bs.size max 1)
      }).sum / content.length).round.toDouble

    def move(graph: Graph, dx: Double): Graph =
      if (dx == 0.0) graph else content.foldLeft(graph)(move_vertex(_, _, dx))

    def combine(that: Region): Region = new Region(content ::: that.content)
  }

  private def pendulum(
    options: Options, metrics: Metrics, levels: List[Level], levels_graph: Graph): Graph =
  {
    def combine_regions(graph: Graph, top_down: Boolean, level: List[Region]): List[Region] =
      level match {
        case r1 :: rest =>
          val rest1 = combine_regions(graph, top_down, rest)
          rest1 match {
            case r2 :: rest2 =>
              val d1 = r1.deflection(graph, top_down)
              val d2 = r2.deflection(graph, top_down)
              if (// Do regions touch?
                  r1.distance(metrics, graph, r2) <= 0.0 &&
                  // Do they influence each other?
                  (d1 <= 0.0 && d2 < d1 || d2 > 0.0 && d1 > d2 || d1 > 0.0 && d2 < 0.0))
                r1.combine(r2) :: rest2
              else r1 :: rest1
            case _ => r1 :: rest1
          }
        case _ => level
      }

    def deflect(level: List[Region], top_down: Boolean, graph: Graph): (Graph, Boolean) =
    {
      level.indices.foldLeft((graph, false)) {
        case ((graph, moved), i) =>
          val r = level(i)
          val d = r.deflection(graph, top_down)
          val dx =
            if (d < 0.0 && i > 0) {
              - (level(i - 1).distance(metrics, graph, r) min (- d))
            }
            else if (d >= 0.0 && i < level.length - 1) {
              r.distance(metrics, graph, level(i + 1)) min d
            }
            else d
          (r.move(graph, dx), moved || d != 0.0)
      }
    }

    val initial_regions = levels.map(level => level.map(l => new Region(List(l))))

    (1 to (2 * options.int("graphview_iterations_pendulum"))).
      foldLeft((levels_graph, initial_regions, true)) {
        case ((graph, regions, moved), iteration) =>
          val top_down = (iteration % 2 == 1)
          if (moved) {
            val (graph1, regions1, moved1) =
              (if (top_down) regions else regions.reverse).
                foldLeft((graph, List.empty[List[Region]], false)) {
                  case ((graph, tops, moved), bot) =>
                    val bot1 = combine_regions(graph, top_down, bot)
                    val (graph1, moved1) = deflect(bot1, top_down, graph)
                    (graph1, bot1 :: tops, moved || moved1)
                }
            (graph1, regions1.reverse, moved1)
          }
          else (graph, regions, moved)
      }._1
  }



  /** rubberband method **/

  private def force_weight(graph: Graph, v: Vertex): Double =
  {
    val preds = graph.imm_preds(v)
    val succs = graph.imm_succs(v)
    val n = preds.size + succs.size
    if (n == 0) 0.0
    else {
      val x = graph.get_node(v).x
      ((preds.iterator ++ succs.iterator).map(w => graph.get_node(w).x - x)).sum / n
    }
  }

  private def rubberband(
    options: Options, metrics: Metrics, levels: List[Level], graph: Graph): Graph =
  {
    val gap = metrics.gap

    (1 to (2 * options.int("graphview_iterations_rubberband"))).foldLeft(graph) {
      case (graph, _) =>
        levels.foldLeft(graph) { case (graph, level) =>
          val m = level.length - 1
          level.iterator.zipWithIndex.foldLeft(graph) {
            case (g, (v, i)) =>
              val d = force_weight(g, v)
              if (d < 0.0 && (i == 0 || vertex_right(g, level(i - 1)) + gap < vertex_left(g, v) + d) ||
                  d > 0.0 && (i == m || vertex_left(g, level(i + 1)) - gap > vertex_right(g, v) + d))
                move_vertex(g, v, d.round.toDouble)
              else g
          }
        }
    }
  }
}

final class Layout private(
  val metrics: Metrics,
  val input_graph: Graph_Display.Graph,
  val output_graph: Layout.Graph)
{
  /* vertex coordinates */

  def translate_vertex(v: Layout.Vertex, dx: Double, dy: Double): Layout =
  {
    if ((dx == 0.0 && dy == 0.0) || !output_graph.defined(v)) this
    else {
      val output_graph1 =
        output_graph.map_node(v, info => info.copy(x = info.x + dx, y = info.y + dy))
      new Layout(metrics, input_graph, output_graph1)
    }
  }


  /* regular nodes */

  def get_node(node: Graph_Display.Node): Layout.Info =
    output_graph.get_node(Layout.Node(node))

  def nodes_iterator: Iterator[Layout.Info] =
    for ((_: Layout.Node, (info, _)) <- output_graph.iterator) yield info


  /* dummies */

  def dummies_iterator: Iterator[Layout.Info] =
    for ((_: Layout.Dummy, (info, _)) <- output_graph.iterator) yield info

  def dummies_iterator(edge: Graph_Display.Edge): Iterator[Layout.Info] =
    new Iterator[Layout.Info] {
      private var index = 0
      def hasNext: Boolean = output_graph.defined(Layout.Dummy(edge._1, edge._2, index))
      def next(): Layout.Info =
      {
        val info = output_graph.get_node(Layout.Dummy(edge._1, edge._2, index))
        index += 1
        info
      }
    }
}

