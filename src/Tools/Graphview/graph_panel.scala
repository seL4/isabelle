/*  Title:      Tools/Graphview/graph_panel.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

GUI panel for graph layout.
*/

package isabelle.graphview


import isabelle._

import java.awt.{Dimension, Graphics2D, Point, Rectangle}
import java.awt.geom.{AffineTransform, Point2D}
import javax.imageio.ImageIO
import javax.swing.{JScrollPane, JComponent, SwingUtilities}
import javax.swing.border.EmptyBorder

import scala.swing.{BorderPanel, Button, CheckBox, Action, FileChooser, Panel, ScrollPane}
import scala.swing.event.{Event, Key, MousePressed, MouseDragged, MouseClicked, MouseEvent}


class Graph_Panel(val graphview: Graphview) extends BorderPanel
{
  graph_panel =>



  /** graph **/

  /* painter */

  private val painter = new Panel
  {
    override def paint(gfx: Graphics2D): Unit =
    {
      super.paintComponent(gfx)

      gfx.setColor(graphview.background_color)
      gfx.fillRect(0, 0, peer.getWidth, peer.getHeight)

      gfx.transform(Transform())
      graphview.paint(gfx)
    }
  }

  def set_preferred_size(): Unit =
  {
    val box = graphview.bounding_box()
    val s = Transform.scale_discrete
    painter.preferredSize = new Dimension((box.width * s).ceil.toInt, (box.height * s).ceil.toInt)
    painter.revalidate()
  }

  def refresh(): Unit =
  {
    if (painter != null) {
      set_preferred_size()
      painter.repaint()
    }
  }

  def scroll_to_node(node: Graph_Display.Node): Unit =
  {
    val gap = graphview.metrics.gap
    val info = graphview.layout.get_node(node)

    val t = Transform()
    val p =
      t.transform(new Point2D.Double(info.x - info.width2 - gap, info.y - info.height2 - gap), null)
    val q =
      t.transform(new Point2D.Double(info.x + info.width2 + gap, info.y + info.height2 + gap), null)

    painter.peer.scrollRectToVisible(
      new Rectangle(p.getX.toInt, p.getY.toInt,
        (q.getX - p.getX).ceil.toInt, (q.getY - p.getY).ceil.toInt))
  }


  /* scrollable graph pane */

  private val graph_pane: ScrollPane = new ScrollPane(painter) {
    tooltip = ""

    override lazy val peer: JScrollPane = new JScrollPane with SuperMixin {
      override def getToolTipText(event: java.awt.event.MouseEvent): String =
        graphview.find_node(Transform.pane_to_graph_coordinates(event.getPoint)) match {
          case Some(node) =>
            graphview.model.full_graph.get_node(node) match {
              case Nil => null
              case content =>
                graphview.make_tooltip(graph_pane.peer, event.getX, event.getY, content)
            }
          case None => null
        }
    }

    horizontalScrollBarPolicy = ScrollPane.BarPolicy.Always
    verticalScrollBarPolicy = ScrollPane.BarPolicy.Always

    listenTo(mouse.moves)
    listenTo(mouse.clicks)
    reactions +=
    {
      case MousePressed(_, p, _, _, _) =>
        Mouse_Interaction.pressed(p)
        painter.repaint()
      case MouseDragged(_, to, _) =>
        Mouse_Interaction.dragged(to)
        painter.repaint()
      case e @ MouseClicked(_, p, m, n, _) =>
        Mouse_Interaction.clicked(p, m, n, SwingUtilities.isRightMouseButton(e.peer))
        painter.repaint()
    }

    contents = painter
  }
  graph_pane.peer.getVerticalScrollBar.setUnitIncrement(10)


  /* transform */

  def rescale(s: Double): Unit =
  {
    Transform.scale = s
    if (zoom != null) zoom.set_item((Transform.scale_discrete * 100).floor.toInt)
    refresh()
  }

  def fit_to_window(): Unit =
  {
    Transform.fit_to_window()
    refresh()
  }

  private object Transform
  {
    private var _scale: Double = 1.0
    def scale: Double = _scale
    def scale_=(s: Double): Unit =
    {
      _scale = (s min 10.0) max 0.1
    }

    def scale_discrete: Double =
    {
      val font_height = GUI.line_metrics(graphview.metrics.font).getHeight.toInt
      (scale * font_height).floor / font_height
    }

    def apply(): AffineTransform =
    {
      val box = graphview.bounding_box()
      val t = AffineTransform.getScaleInstance(scale_discrete, scale_discrete)
      t.translate(- box.x, - box.y)
      t
    }

    def fit_to_window(): Unit =
    {
      if (graphview.visible_graph.is_empty)
        rescale(1.0)
      else {
        val box = graphview.bounding_box()
        rescale((size.width / box.width) min (size.height / box.height))
      }
    }

    def pane_to_graph_coordinates(at: Point2D): Point2D =
    {
      val s = Transform.scale_discrete
      val p = Transform().inverseTransform(graph_pane.peer.getViewport.getViewPosition, null)

      p.setLocation(p.getX + at.getX / s, p.getY + at.getY / s)
      p
    }
  }


  /* interaction */

  graphview.model.Colors.events += { case _ => painter.repaint() }
  graphview.model.Mutators.events += { case _ => painter.repaint() }

  private object Mouse_Interaction
  {
    private var draginfo: (Point, List[Graph_Display.Node], List[Layout.Dummy]) =
      (new Point(0, 0), Nil, Nil)

    def pressed(at: Point): Unit =
    {
      val c = Transform.pane_to_graph_coordinates(at)
      val l =
        graphview.find_node(c) match {
          case Some(node) =>
            if (graphview.Selection.contains(node)) graphview.Selection.get()
            else List(node)
          case None => Nil
        }
      val d =
        l match {
          case Nil => graphview.find_dummy(c).toList
          case _ => Nil
        }
      draginfo = (at, l, d)
    }

    def dragged(to: Point): Unit =
    {
      val (from, p, d) = draginfo

      val s = Transform.scale_discrete
      val dx = to.x - from.x
      val dy = to.y - from.y

      (p, d) match {
        case (Nil, Nil) =>
          val r = graph_pane.peer.getViewport.getViewRect
          r.translate(- dx, - dy)
          painter.peer.scrollRectToVisible(r)

        case (Nil, ds) =>
          ds.foreach(d => graphview.translate_vertex(d, dx / s, dy / s))

        case (ls, _) =>
          ls.foreach(l => graphview.translate_vertex(Layout.Node(l), dx / s, dy / s))
      }

      draginfo = (to, p, d)
    }

    def clicked(at: Point, m: Key.Modifiers, clicks: Int, right_click: Boolean): Unit =
    {
      val c = Transform.pane_to_graph_coordinates(at)

      if (clicks < 2) {
        if (right_click) {
          // FIXME
          if (false) {
            val menu = Popups(graph_panel, graphview.find_node(c), graphview.Selection.get())
            menu.show(graph_pane.peer, at.x, at.y)
          }
        }
        else {
          (graphview.find_node(c), m) match {
            case (Some(node), Key.Modifier.Control) => graphview.Selection.add(node)
            case (None, Key.Modifier.Control) =>

            case (Some(node), Key.Modifier.Shift) => graphview.Selection.add(node)
            case (None, Key.Modifier.Shift) =>

            case (Some(node), _) =>
              graphview.Selection.clear()
              graphview.Selection.add(node)
            case (None, _) =>
              graphview.Selection.clear()
          }
        }
      }
    }
  }



  /** controls **/

  private val mutator_dialog =
    new Mutator_Dialog(graphview, graphview.model.Mutators, "Filters", "Hide", false)
  private val color_dialog =
    new Mutator_Dialog(graphview, graphview.model.Colors, "Colorations")

  private val chooser = new FileChooser {
    fileSelectionMode = FileChooser.SelectionMode.FilesOnly
    title = "Save image (.png or .pdf)"
  }

  private val show_content = new CheckBox() {
    selected = graphview.show_content
    action = Action("Show content") {
      graphview.show_content = selected
      graphview.update_layout()
      refresh()
    }
    tooltip = "Show full node content within graph layout"
  }

  private val show_arrow_heads = new CheckBox() {
    selected = graphview.show_arrow_heads
    action = Action("Show arrow heads") {
      graphview.show_arrow_heads = selected
      painter.repaint()
    }
    tooltip = "Draw edges with explicit arrow heads"
  }

  private val show_dummies = new CheckBox() {
    selected = graphview.show_dummies
    action = Action("Show dummies") {
      graphview.show_dummies = selected
      painter.repaint()
    }
    tooltip = "Draw dummy nodes within graph layout, for easier mouse dragging"
  }

  private val save_image = new Button {
    action = Action("Save image") {
      chooser.showSaveDialog(this) match {
        case FileChooser.Result.Approve =>
          try { Graph_File.write(chooser.selectedFile, graphview) }
          catch {
            case ERROR(msg) => GUI.error_dialog(this.peer, "Error", GUI.scrollable_text(msg))
          }
        case _ =>
      }
    }
    tooltip = "Save current graph layout as PNG or PDF"
  }

  private val zoom = new GUI.Zoom_Box { def changed = rescale(0.01 * factor) }

  private val fit_window = new Button {
    action = Action("Fit to window") { fit_to_window() }
    tooltip = "Zoom to fit window width and height"
  }

  private val update_layout = new Button {
    action = Action("Update layout") {
      graphview.update_layout()
      refresh()
    }
    tooltip = "Regenerate graph layout according to built-in algorithm"
  }

  private val editor_style = new CheckBox() {
    selected = graphview.editor_style
    action = Action("Editor style") {
      graphview.editor_style = selected
      graphview.update_layout()
      refresh()
    }
    tooltip = "Use editor font and colors for painting"
  }

  private val colorations = new Button { action = Action("Colorations") { color_dialog.open } }
  private val filters = new Button { action = Action("Filters") { mutator_dialog.open } }

  private val controls =
    Wrap_Panel(
      List(show_content, show_arrow_heads, show_dummies,
        save_image, zoom, fit_window, update_layout, editor_style)) // FIXME colorations, filters



  /** main layout **/

  layout(graph_pane) = BorderPanel.Position.Center
  layout(controls) = BorderPanel.Position.North

  rescale(1.0)
}
