/*  Title:      Tools/Graphview/src/layout_pendulum.scala
    Author:     Markus Kaiser, TU Muenchen

Pendulum DAG layout algorithm.
*/

package isabelle.graphview


import isabelle._


object Layout_Pendulum {
  type Key = String
  type Entry = Option[Locale]
  type Point = (Double, Double)
  type Coordinates = Map[Key, Point]
  type Level = List[Key]
  type Levels = List[Level]
  type Layout = (Coordinates, Map[(Key, Key), List[Point]])
  type Dummies = (Graph[Key, Entry], List[Key], Map[Key, Int])
  
  val x_distance = 350
  val y_distance = 350
  val pendulum_iterations = 10
  
  def apply(graph: Graph[Key, Entry]): Layout = {
    if (graph.entries.isEmpty)
      (Map[Key, Point](), Map[(Key, Key), List[Point]]())
    else {
      val (dummy_graph, dummies, dummy_levels) = {
        val initial_levels = level_map(graph)

        def add_dummies(graph: Graph[Key, Entry], from: Key, to: Key,
                        levels: Map[Key, Int]): Dummies = {
          val ds = 
            ((levels(from) + 1) until levels(to))
            .map("%s$%s$%d" format (from, to, _)).toList

          val ls = 
            (levels /: ((levels(from) + 1) until levels(to)).zip(ds)) {
              case (ls, (l, d)) => ls + (d -> l)
            }

          val next_nodes = 
            (graph /: ds) {
              (graph, d) => graph.new_node(d, None)
            }

          val next =
            (next_nodes.del_edge(from, to) /: (from :: ds ::: List(to)).sliding(2)) {
                case (graph, List(f, t)) => graph.add_edge(f, t)
            }
          (next, ds, ls)
        }

        ((graph, Map[(Key, Key), List[Key]](), initial_levels) /: graph.keys) {
          case ((graph, dummies, levels), from) => {
            ((graph, dummies, levels) /: graph.imm_succs(from)) {
              case ((graph, dummies, levels), to) => {
                  if (levels(to) - levels(from) <= 1) (graph, dummies, levels)
                  else add_dummies(graph, from, to, levels) match {
                    case (next, ds, ls) => (next, dummies + ((from, to) -> ds), ls)
                  }
              }
            }
          }
        }
      }
      
      val levels =
        minimize_crossings(
          dummy_graph,
          level_list(dummy_levels)
        )

      val coords =
        pendulum(dummy_graph,
                levels,
                initial_coordinates(levels)
        )

      val dummy_coords = 
        (Map[(Key, Key), List[Point]]() /: dummies.keys) {
          case (map, key) => map + (key -> dummies(key).map(coords(_)))
        }

      (coords, dummy_coords)
    }
  }
  
  def level_map(graph: Graph[Key, Entry]): Map[Key, Int] = 
    (Map[Key, Int]() /: graph.topological_order){
      (levels, key) => {
        val pred_levels = graph.imm_preds(key).map(levels(_)) + (-1)
        levels + (key -> (pred_levels.max + 1))
      }}
  
  def level_list(map: Map[Key, Int]): Levels =
    (map.toList.sortBy(_._2) :\ List[(Int, Level)]()){
        case ((key, i), list) => {
            if (list.isEmpty) (i, List(key)) :: list
            else {
              val (j, l) = list.head
              if (i == j) (i, key :: l) :: list.tail
              else (i, List(key)) :: list
            }
        }
    }.map(_._2)
  
  def count_crossings(graph: Graph[Key, Entry], levels: Levels): Int = {
    def in_level(ls: Levels): Int = ls match {
      case List(top, bot) =>
        top.zipWithIndex.map{
          case (outer_parent, outer_parent_index) => 
            graph.imm_succs(outer_parent).map(bot.indexOf(_))
            .map(outer_child => {
              (0 until outer_parent_index)
              .map(inner_parent => 
                graph.imm_succs(top(inner_parent))
                .map(bot.indexOf(_))
                .filter(inner_child => outer_child < inner_child)
                .size
              ).sum
            }).sum
        }.sum
      
      case _ => 0
    }
    
    levels.sliding(2).map(in_level).sum
  }
  
  def minimize_crossings(graph: Graph[Key, Entry], levels: Levels): Levels = {
    def resort_level(parent: Level, child: Level, top_down: Boolean): Level = 
      child.map(k => {
          val ps = if (top_down) graph.imm_preds(k) else graph.imm_succs(k)
          val weight = 
            (0d /: ps) {
              (w, p) => w + math.max(0, parent.indexOf(p))
            } / math.max(ps.size, 1)
          (k, weight)
      }).sortBy(_._2).map(_._1)
    
    def resort(levels: Levels, top_down: Boolean) = top_down match {
      case true =>
        (List[Level](levels.head) /: levels.tail) {
          (tops, bot) => resort_level(tops.head, bot, top_down) :: tops
        }.reverse
        
      case false => 
        (List[Level](levels.reverse.head) /: levels.reverse.tail) {
          (bots, top) => resort_level(bots.head, top, top_down) :: bots
        }
      }
    
    ((levels, count_crossings(graph, levels), true) /: (1 to 40)) {
      case ((old_levels, old_crossings, top_down), _) => {
          val new_levels = resort(old_levels, top_down)
          val new_crossings = count_crossings(graph, new_levels)
          if ( new_crossings < old_crossings)
            (new_levels, new_crossings, !top_down)
          else
            (old_levels, old_crossings, !top_down)
      }
    }._1
  }
  
  def initial_coordinates(levels: Levels): Coordinates =
    (Map[Key, Point]() /: levels.reverse.zipWithIndex){
      case (coords, (level, yi)) =>
        (coords /: level.zipWithIndex) {
          case (coords, (node, xi)) => 
            coords + (node -> (xi * x_distance, yi * y_distance))
        }
    }
  
  def pendulum(graph: Graph[Key, Entry],
               levels: Levels, coords: Map[Key, Point]): Coordinates =
  {
    type Regions = List[List[Region]]
    
    def iteration(regions: Regions, coords: Coordinates,
                  top_down: Boolean): (Regions, Coordinates, Boolean) =
    { 
      val (nextr, nextc, moved) = 
      ((List[List[Region]](), coords, false) /:
       (if (top_down) regions else regions.reverse)) {
        case ((tops, coords, prev_moved), bot) => {
            val nextb = collapse(coords, bot, top_down)
            val (nextc, this_moved) = deflect(coords, nextb, top_down)
            (nextb :: tops, nextc, prev_moved || this_moved)
        }
      }
    
      (nextr.reverse, nextc, moved)
    }
    
    def collapse(coords: Coordinates, level: List[Region],
                 top_down: Boolean): List[Region] = 
      if (level.size <= 1) level
      else {
        var next = level
        var regions_changed = true
        while (regions_changed) {
          regions_changed = false
          for (i <- (next.length to 1)) {
            val (r1, r2) = (next(i-1), next(i))
            val d1 = r1.deflection(coords, top_down)
            val d2 = r2.deflection(coords, top_down)

            if (
                // Do regions touch?
                r1.distance(coords, r2) <= x_distance &&
                // Do they influence each other?
                (d1 <= 0 && d2 < d1 || d2 > 0 && d1 > d2 || d1 > 0 && d2 < 0)
                )
            {
              regions_changed = true
              r1.nodes = r1.nodes ::: r2.nodes
              next = next.filter(next.indexOf(_) != i)
            }            
          }
        }
        next
      }
    
    def deflect(coords: Coordinates, level: List[Region],
                top_down: Boolean): (Coordinates, Boolean) =
      ((coords, false) /: (0 until level.length)) {
        case ((coords, moved), i) => {
            val r = level(i)
            val d = r.deflection(coords, top_down)
            val offset = {
              if (i == 0 && d <= 0) d
              else if (i == level.length - 1 && d >= 0) d
              else if (d < 0) {
                val prev = level(i-1)
                math.max( -(r.distance(coords, prev) - x_distance), d )
              }
              else {
                val next = level(i+1)
                math.min( r.distance(coords, next) - x_distance, d )
              }
            }
            
            (r.move(coords, offset), moved || (d != 0))
        }
      }
    
    val regions = levels.map(level => level.map(new Region(graph, _)))
    
    ((regions, coords, true, true) /: (1 to pendulum_iterations)) {
      case ((regions, coords, top_down, moved), _) => 
        if (moved) {
          val (nextr, nextc, m) = iteration(regions, coords, top_down)
          (nextr, nextc, !top_down, m)
        }
        else (regions, coords, !top_down, moved)
    }._2
  }
  
  protected class Region(val graph: Graph[Key, Entry], node: Key) {
    var nodes: List[Key] = List(node)
       
    def left(coords: Coordinates): Double =
      nodes.map(coords(_)._1).min
    def right(coords: Coordinates): Double =
      nodes.map(coords(_)._1).max
    def distance(coords: Coordinates, to: Region): Double =
      math.min(math.abs(left(coords) - to.left(coords)),
               math.abs(right(coords) - to.right(coords)))
    
    def deflection(coords: Coordinates, use_preds: Boolean) = 
      nodes.map(k => (coords(k)._1,
                      if (use_preds) graph.imm_preds(k).toList
                      else graph.imm_succs(k).toList))
      .map({case (x, as) => as.map(coords(_)._1 - x).sum / math.max(as.length, 1)})
      .sum / nodes.length
    
    def move(coords: Coordinates, by: Double): Coordinates = 
      (coords /: nodes) {
        (cs, node) => {
          val (x, y) = cs(node)
          cs + (node -> (x + by, y))
        }
      }
  }
}
