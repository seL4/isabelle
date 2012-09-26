/*  Title:      Tools/Graphview/src/graph_panel.scala
    Author:     Markus Kaiser, TU Muenchen

Graphview Java2D drawing panel.
*/

package isabelle.graphview

import isabelle._

import java.awt.{Dimension, Graphics2D, Point, Rectangle}
import java.awt.geom.{AffineTransform, Point2D}
import javax.swing.ToolTipManager
import scala.swing.{Panel, ScrollPane}
import scala.swing.event._


class Graph_Panel(private val vis: Visualizer) extends ScrollPane {
  this.peer.setWheelScrollingEnabled(false)
  focusable = true
  requestFocus()
  
  horizontalScrollBarPolicy = ScrollPane.BarPolicy.Always
  verticalScrollBarPolicy = ScrollPane.BarPolicy.Always
  
  def visualizer = vis
  
  def fit_to_window() = {
    Transform.fit_to_window()
    repaint()
  }
  
  def apply_layout() = vis.Coordinates.layout()  

  private val paint_panel = new Panel {    
    def set_preferred_size() {
        val (minX, minY, maxX, maxY) = vis.Coordinates.bounds()
        val s = Transform.scale
        val (px, py) = Transform.padding

        preferredSize = new Dimension((math.abs(maxX - minX + px) * s).toInt,
                                      (math.abs(maxY - minY + py) * s).toInt)
        
        revalidate()
      }  
    
    override def paint(g: Graphics2D) {
      set_preferred_size()
      super.paintComponent(g)
      g.transform(Transform())
      
      vis.Drawer.paint_all_visible(g, true)
    }
  }
  contents = paint_panel
  
  listenTo(keys)
  listenTo(mouse.moves)
  listenTo(mouse.clicks)
  listenTo(mouse.wheel)
  reactions += Interaction.Mouse.react
  reactions += Interaction.Keyboard.react
  reactions += {
      case KeyTyped(_, _, _, _) => {repaint(); requestFocus()}
      case MousePressed(_, _, _, _, _) => {repaint(); requestFocus()}
      case MouseDragged(_, _, _) => {repaint(); requestFocus()}
      case MouseWheelMoved(_, _, _, _) => {repaint(); requestFocus()}
      case MouseClicked(_, _, _, _, _) => {repaint(); requestFocus()}
      case MouseMoved(_, _, _) => repaint()
    }
  private val r = {
    import scala.actors.Actor._
    
    actor {
      loop {
        react {
          // FIXME Swing thread!?
          case _ => repaint()
        }
      }
    }
  }
  vis.model.Colors.events += r
  vis.model.Mutators.events += r
  ToolTipManager.sharedInstance.setDismissDelay(1000*60*60)
  
  apply_layout()
  fit_to_window()
  
  protected object Transform {
    val padding = (4000, 2000)
    
    private var _scale = 1d
    def scale = _scale
    def scale_= (s: Double) = {
                  _scale = math.max(math.min(s, 10), 0.01)
                  paint_panel.set_preferred_size()
                }
                
    def apply() = {
      val (minX, minY, _, _) = vis.Coordinates.bounds()
      
      val at = AffineTransform.getScaleInstance(scale, scale)
      at.translate(-minX + padding._1 / 2, -minY + padding._2 / 2)
      at
    }
    
    def fit_to_window() {
      if (vis.model.visible_nodes().isEmpty)
        scale = 1
      else {
        val (minX, minY, maxX, maxY) = vis.Coordinates.bounds()

        val (dx, dy) = (maxX - minX + padding._1, maxY - minY + padding._2)
        val (sx, sy) = (1d * size.width / dx, 1d * size.height / dy)
        scale = math.min(sx, sy)
      }
    }
    
    def pane_to_graph_coordinates(at: Point2D): Point2D = {
      val s = Transform.scale
      val p = Transform().inverseTransform(peer.getViewport.getViewPosition, null)
      
      p.setLocation(p.getX + at.getX / s, p.getY + at.getY / s)
      p
    }
  }
  
  private val panel = this
  object Interaction {
    object Keyboard {
      import scala.swing.event.Key._
      
      val react: PartialFunction[Event, Unit] = {
        case KeyTyped(_, c, m, _) => typed(c, m)
      }      
      
      def typed(c: Char, m: Modifiers) = (c, m) match {
        case ('+', _) => {
          Transform.scale *= 5d/4
        }

        case ('-', _) => {
          Transform.scale *= 4d/5
        }

        case ('0', _) => {
          Transform.fit_to_window()
        }
        
        case('1', _) => {
            vis.Coordinates.layout()
        }

        case('2', _) => {
            Transform.fit_to_window()
        }          
          
        case _ =>
      }
    }
    
    object Mouse {
      import java.awt.image.BufferedImage
      import scala.swing.event.Key.Modifier._
      type Modifiers = Int
      type Dummy = ((String, String), Int)
      
      private var draginfo: (Point, Iterable[String], Iterable[Dummy]) = null
      private val g =
        new BufferedImage(1, 1, BufferedImage.TYPE_INT_RGB).createGraphics
      g.setFont(vis.Font())
      g.setRenderingHints(vis.rendering_hints)

      val react: PartialFunction[Event, Unit] = {   
        case MousePressed(_, p, _, _, _) => pressed(p)
        case MouseDragged(_, to, _) => {
            drag(draginfo, to)
            val (_, p, d) = draginfo
            draginfo = (to, p, d)
          }
        case MouseWheelMoved(_, p, _, r) => wheel(r, p)
        case e@MouseClicked(_, p, m, n, _) => click(p, m, n, e)
        case MouseMoved(_, p, _) => moved(p)
      }
      
      def node(at: Point2D): Option[String] = 
        vis.model.visible_nodes().find({
            l => vis.Drawer.shape(g, Some(l)).contains(at)
          })
      
      def dummy(at: Point2D): Option[Dummy] =
        vis.model.visible_edges().map({
            i => vis.Coordinates(i).zipWithIndex.map((i, _))
          }).flatten.find({
            case (_, ((x, y), _)) => 
              vis.Drawer.shape(g, None).contains(at.getX() - x, at.getY() - y)
          }) match {
            case None => None
            case Some((name, (_, index))) => Some((name, index))
          }
      
      def moved(at: Point) {
        val c = Transform.pane_to_graph_coordinates(at)
        node(c) match {
          case Some(l) => panel.tooltip = vis.Tooltip.text(l, g.getFontMetrics)
          case None => panel.tooltip = null
        }
      }
      
      def pressed(at: Point) {
        val c = Transform.pane_to_graph_coordinates(at)
        val l = node(c) match {
          case Some(l) => if (vis.Selection(l))
                            vis.Selection()
                          else
                            List(l)
          
          case None => Nil
        }
        val d = l match {
          case Nil => dummy(c) match {
              case Some(d) => List(d)
              case None => Nil
          }
          
          case _ => Nil
        }
        
        draginfo = (at, l, d)
      }
      
      def click(at: Point, m: Modifiers, clicks: Int, e: MouseEvent) {
        import javax.swing.SwingUtilities
        
        val c = Transform.pane_to_graph_coordinates(at)
        val p = node(c)
        
        def left_click() {
          (p, m) match {
            case (Some(l), Control) => vis.Selection.add(l)
            case (None, Control) =>

            case (Some(l), Shift) => vis.Selection.add(l)
            case (None, Shift) =>

            case (Some(l), _) => vis.Selection.set(List(l))
            case (None, _) => vis.Selection.clear
          }          
        }
        
        def right_click() {
          val menu = Popups(panel, p, vis.Selection())
          menu.show(panel.peer, at.x, at.y)
        }
        
        def double_click() {
          p match {
            case Some(l) => {
                val p = at.clone.asInstanceOf[Point]
                SwingUtilities.convertPointToScreen(p, panel.peer)
                new Floating_Dialog(
                  vis.Tooltip.content(l),
                  vis.Caption(l),
                  at
                ).open
            }
            
            case None =>
          }          
        }
        
        if (clicks < 2) {
          if (SwingUtilities.isRightMouseButton(e.peer)) right_click()
          else left_click()
        } else if (clicks == 2) {
          if (SwingUtilities.isLeftMouseButton(e.peer)) double_click()
        }
      }   

      def drag(draginfo: (Point, Iterable[String], Iterable[Dummy]), to: Point) {
        val (from, p, d) = draginfo

        val s = Transform.scale
        val (dx, dy) = (to.x - from.x, to.y - from.y)        
        (p, d) match {
          case (Nil, Nil) => {
            val r = panel.peer.getViewport.getViewRect
            r.translate(-dx, -dy)

            paint_panel.peer.scrollRectToVisible(r)
          }
            
          case (Nil, ds) =>
            ds.foreach(d => vis.Coordinates.translate(d, (dx / s, dy / s)))
                     
          case (ls, _) =>
            ls.foreach(l => vis.Coordinates.translate(l, (dx / s, dy / s)))
        }
      }

      def wheel(rotation: Int, at: Point) {
        val at2 = Transform.pane_to_graph_coordinates(at)
        // > 0 -> up
        Transform.scale *= (if (rotation > 0) 4d/5 else 5d/4)

        // move mouseposition to center
        Transform().transform(at2, at2)
        val r = panel.peer.getViewport.getViewRect
        val (width, height) = (r.getWidth, r.getHeight)
        paint_panel.peer.scrollRectToVisible(
          new Rectangle((at2.getX() - width / 2).toInt,
                        (at2.getY() - height / 2).toInt,
                        width.toInt,
                        height.toInt)
        )
      }
    }
  }
}
