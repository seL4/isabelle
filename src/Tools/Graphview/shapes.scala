/*  Title:      Tools/Graphview/shapes.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Drawable shapes.
*/

package isabelle.graphview


import isabelle._

import java.awt.{BasicStroke, Graphics2D, Shape}
import java.awt.geom.{AffineTransform, GeneralPath, Path2D, Rectangle2D,
  RoundRectangle2D, PathIterator}


object Shapes
{
  private val default_stroke =
    new BasicStroke(1, BasicStroke.CAP_BUTT, BasicStroke.JOIN_ROUND)

  def shape(info: Layout.Info): Rectangle2D.Double =
    new Rectangle2D.Double(info.x - info.width2, info.y - info.height2, info.width, info.height)

  def highlight_node(gfx: Graphics2D, graphview: Graphview, node: Graph_Display.Node): Unit =
  {
    val metrics = graphview.metrics
    val extra = metrics.char_width
    val info = graphview.layout.get_node(node)

    gfx.setColor(graphview.highlight_color)
    gfx.fill(new Rectangle2D.Double(
      info.x - info.width2 - extra,
      info.y - info.height2 - extra,
      info.width + 2 * extra,
      info.height + 2 * extra))
  }

  def paint_node(gfx: Graphics2D, graphview: Graphview, node: Graph_Display.Node): Unit =
  {
    val metrics = graphview.metrics
    val info = graphview.layout.get_node(node)
    val c = graphview.node_color(node)
    val s = shape(info)

    gfx.setColor(c.background)
    gfx.fill(s)

    gfx.setColor(c.border)
    gfx.setStroke(default_stroke)
    gfx.draw(s)

    gfx.setColor(c.foreground)
    gfx.setFont(metrics.font)

    val text_width =
      info.lines.foldLeft(0.0) { case (w, line) => w max metrics.string_bounds(line).getWidth }
    val text_height =
      (info.lines.length max 1) * metrics.height.ceil
    val x = (s.getCenterX - text_width / 2).round.toInt
    var y = (s.getCenterY - text_height / 2 + metrics.ascent).round.toInt
    for (line <- info.lines) {
      gfx.drawString(Word.bidi_override(line), x, y)
      y += metrics.height.ceil.toInt
    }
  }

  def paint_dummy(gfx: Graphics2D, graphview: Graphview, info: Layout.Info): Unit =
  {
    gfx.setStroke(default_stroke)
    gfx.setColor(graphview.dummy_color)
    gfx.draw(shape(info))
  }

  object Straight_Edge
  {
    def paint(gfx: Graphics2D, graphview: Graphview, edge: Graph_Display.Edge): Unit =
    {
      val p = graphview.layout.get_node(edge._1)
      val q = graphview.layout.get_node(edge._2)
      val ds =
      {
        val a = p.y min q.y
        val b = p.y max q.y
        graphview.layout.dummies_iterator(edge).filter(d => a < d.y && d.y < b).toList
      }
      val path = new GeneralPath(Path2D.WIND_EVEN_ODD, ds.length + 2)

      path.moveTo(p.x, p.y)
      ds.foreach(d => path.lineTo(d.x, d.y))
      path.lineTo(q.x, q.y)

      if (graphview.show_dummies) ds.foreach(paint_dummy(gfx, graphview, _))

      gfx.setStroke(default_stroke)
      gfx.setColor(graphview.edge_color(edge, p.y < q.y))
      gfx.draw(path)

      if (graphview.show_arrow_heads) Arrow_Head.paint(gfx, path, Shapes.shape(q))
    }
  }

  object Cardinal_Spline_Edge
  {
    private val slack = 0.1

    def paint(gfx: Graphics2D, graphview: Graphview, edge: Graph_Display.Edge): Unit =
    {
      val p = graphview.layout.get_node(edge._1)
      val q = graphview.layout.get_node(edge._2)
      val ds =
      {
        val a = p.y min q.y
        val b = p.y max q.y
        graphview.layout.dummies_iterator(edge).filter(d => a < d.y && d.y < b).toList
      }

      if (ds.isEmpty) Straight_Edge.paint(gfx, graphview, edge)
      else {
        val path = new GeneralPath(Path2D.WIND_EVEN_ODD, ds.length + 2)
        path.moveTo(p.x, p.y)

        val coords = p :: ds ::: List(q)
        val dx = coords(2).x - coords(0).x
        val dy = coords(2).y - coords(0).y

        val (dx2, dy2) =
          coords.sliding(3).foldLeft((dx, dy)) {
            case ((dx, dy), List(l, m, r)) =>
              val dx2 = r.x - l.x
              val dy2 = r.y - l.y
              path.curveTo(
                l.x + slack * dx, l.y + slack * dy,
                m.x - slack * dx2, m.y - slack * dy2,
                m.x, m.y)
              (dx2, dy2)
          }

        val l = ds.last
        path.curveTo(
          l.x + slack * dx2, l.y + slack * dy2,
          q.x - slack * dx2, q.y - slack * dy2,
          q.x, q.y)

        if (graphview.show_dummies) ds.foreach(paint_dummy(gfx, graphview, _))

        gfx.setStroke(default_stroke)
        gfx.setColor(graphview.edge_color(edge, p.y < q.y))
        gfx.draw(path)

        if (graphview.show_arrow_heads) Arrow_Head.paint(gfx, path, Shapes.shape(q))
      }
    }
  }

  object Arrow_Head
  {
    type Point = (Double, Double)

    private def position(path: GeneralPath, shape: Shape): Option[AffineTransform] =
    {
      def intersecting_line(path: GeneralPath, shape: Shape): Option[(Point, Point)] =
      {
        val i = path.getPathIterator(null, 1.0)
        val seg = Array[Double](0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
        var p1 = (0.0, 0.0)
        var p2 = (0.0, 0.0)
        while (!i.isDone) {
          i.currentSegment(seg) match {
            case PathIterator.SEG_MOVETO => p2 = (seg(0), seg(1))
            case PathIterator.SEG_LINETO =>
              p1 = p2
              p2 = (seg(0), seg(1))

              if(shape.contains(seg(0), seg(1)))
                return Some((p1, p2))
            case _ =>
          }
          i.next()
        }
        None
      }

      def binary_search(line: (Point, Point), shape: Shape): Option[AffineTransform] =
      {
        val ((fx, fy), (tx, ty)) = line
        if (shape.contains(fx, fy) == shape.contains(tx, ty))
          None
        else {
          val (dx, dy) = (fx - tx, fy - ty)
          if ((dx * dx + dy * dy) < 1.0) {
            val at = AffineTransform.getTranslateInstance(fx, fy)
            at.rotate(- (math.atan2(dx, dy) + math.Pi / 2))
            Some(at)
          }
          else {
            val (mx, my) = (fx + (tx - fx) / 2.0, fy + (ty - fy) / 2.0)
            if (shape.contains(fx, fy) == shape.contains(mx, my))
              binary_search(((mx, my), (tx, ty)), shape)
            else
              binary_search(((fx, fy), (mx, my)), shape)
          }
        }
      }

      intersecting_line(path, shape) match {
        case None => None
        case Some(line) => binary_search(line, shape)
      }
    }

    def paint(gfx: Graphics2D, path: GeneralPath, shape: Shape): Unit =
    {
      position(path, shape) match {
        case None =>
        case Some(at) =>
          val arrow = new GeneralPath(Path2D.WIND_EVEN_ODD, 3)
          arrow.moveTo(0, 0)
          arrow.lineTo(-10, 4)
          arrow.lineTo(-6, 0)
          arrow.lineTo(-10, -4)
          arrow.lineTo(0, 0)
          arrow.transform(at)
          gfx.fill(arrow)
      }
    }
  }
}
