/*  Title:      Tools/Graphview/src/visualizer.scala
    Author:     Markus Kaiser, TU Muenchen

Graph visualization interface.
*/

package isabelle.graphview


import isabelle._


import java.awt.{Font => JFont, Color => JColor, Shape}
import java.awt.{RenderingHints, Graphics2D}
import javax.swing.JComponent


class Visualizer(val model: Model) {
  object Coordinates {
    private var nodes = Map[String, (Double, Double)]()
    private var dummies = Map[(String, String), List[(Double, Double)]]()
    
    def apply(k: String): (Double, Double) = nodes.get(k) match {
      case Some(c) => c
      case None => (0, 0)
    }
    
    def apply(e: (String, String)): List[(Double, Double)] = dummies.get(e) match {
      case Some(ds) => ds
      case None => Nil
    }
    
    def translate(k: String, by: (Double, Double)) {
      val ((x, y), (dx, dy)) = (Coordinates(k), by)
      reposition(k, (x + dx, y + dy))
    }
    
    def reposition(k: String, to: (Double, Double)) {
      nodes += (k -> to)
    }
    
    def translate(d: ((String, String), Int), by: (Double, Double)) {
      val ((e, i),(dx, dy)) = (d, by)
      val (x, y) = apply(e)(i)
      reposition(d, (x + dx, y + dy))
    }
    
    def reposition(d: ((String, String), Int), to: (Double, Double)) {
      val (e, index) = d
      dummies.get(e) match {
        case None =>
        case Some(ds) =>
          dummies += ( e ->
            (ds.zipWithIndex :\ List[(Double, Double)]()){
              case ((t, i), n) => if (index == i) to :: n
                                  else t :: n
            }
          )
      }
    }
    
    def layout() {
      val (l, d) = Layout_Pendulum(model.current)
      nodes = l
      dummies = d
    }
    
    def bounds(): (Double, Double, Double, Double) = 
      model.visible_nodes().toList match {
        case Nil => (0, 0, 0, 0)
        case nodes => {
          val X: (String => Double) = {n => apply(n)._1}
          val Y: (String => Double) = {n => apply(n)._2}

          (X(nodes.minBy(X)), Y(nodes.minBy(Y)),
            X(nodes.maxBy(X)), Y(nodes.maxBy(Y)))              
        }
      }
  }
  
  private val visualizer = this
  object Drawer
  {
    import Shapes._
    
    def apply(g: Graphics2D, n: Option[String]) = n match {
      case None => 
      case Some(_) => Growing_Node.paint(g, visualizer, n)
    }
    
    def apply(g: Graphics2D, e: (String, String), head: Boolean, dummies: Boolean) = {
      Cardinal_Spline_Edge.paint(g, visualizer, e, head, dummies)
    }
    
    def paint_all_visible(g: Graphics2D, dummies: Boolean)
    {
      g.setFont(Font())

      g.setRenderingHints(rendering_hints)

      model.visible_edges().foreach(e => {
          apply(g, e, Parameters.arrow_heads, dummies)
        })

      model.visible_nodes().foreach(l => {
          apply(g, Some(l))
        })
    }
    
    def shape(g: Graphics2D, n: Option[String]): Shape = n match {
      case None => Dummy.shape(g, visualizer, None)
      case Some(_) => Growing_Node.shape(g, visualizer, n)
    }
  }
  
  object Selection {
    private var selected: List[String] = Nil
    
    def apply() = selected
    def apply(s: String) = selected.contains(s)
    
    def add(s: String) { selected = s :: selected }
    def set(ss: List[String]) { selected = ss }
    def clear() { selected = Nil }
  }
  
  object Color
  {
    def apply(l: Option[String]): (JColor, JColor, JColor) = l match {
      case None => (JColor.GRAY, JColor.WHITE, JColor.BLACK)
      case Some(c) => {
          if (Selection(c))
            (JColor.BLUE, JColor.GREEN, JColor.BLACK)
          else
            (JColor.BLACK,
             model.colors.getOrElse(c, JColor.WHITE), JColor.BLACK)
      }
    }
      
    def apply(e: (String, String)): JColor = JColor.BLACK
  }  

  object Font
  {
    def apply(): JFont =
      new JFont(Parameters.font_family, JFont.BOLD, Parameters.font_size)
  }
  
  object Caption {    
    def apply(key: String) =
      if (Parameters.long_names) key
      else model.complete.get_node(key).name
  }

  val rendering_hints =
    new RenderingHints(
      RenderingHints.KEY_ANTIALIASING,
      RenderingHints.VALUE_ANTIALIAS_ON)
}