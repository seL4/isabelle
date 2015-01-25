/*  Title:      Tools/Graphview/graph_panel.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Graphview Java2D drawing panel.
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


class Graph_Panel(val visualizer: Visualizer) extends BorderPanel
{
  graph_panel =>



  /** graph **/

  /* painter */

  private val painter = new Panel
  {
    override def paint(gfx: Graphics2D)
    {
      super.paintComponent(gfx)

      gfx.setColor(visualizer.background_color)
      gfx.fillRect(0, 0, peer.getWidth, peer.getHeight)

      gfx.transform(Transform())
      visualizer.paint_all_visible(gfx)
    }
  }

  def set_preferred_size()
  {
    val box = visualizer.bounding_box()
    val s = Transform.scale_discrete
    painter.preferredSize = new Dimension((box.width * s).ceil.toInt, (box.height * s).ceil.toInt)
    painter.revalidate()
  }

  def refresh()
  {
    if (painter != null) {
      set_preferred_size()
      painter.repaint()
    }
  }

  def scroll_to_node(node: Graph_Display.Node)
  {
    val gap = visualizer.metrics.gap
    val info = visualizer.layout.get_node(node)

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
        visualizer.find_node(Transform.pane_to_graph_coordinates(event.getPoint)) match {
          case Some(node) =>
            visualizer.model.full_graph.get_node(node) match {
              case Nil => null
              case content =>
                visualizer.make_tooltip(graph_pane.peer, event.getX, event.getY, content)
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

  def rescale(s: Double)
  {
    Transform.scale = s
    if (zoom != null) zoom.set_item((Transform.scale_discrete * 100).floor.toInt)
    refresh()
  }

  def fit_to_window()
  {
    Transform.fit_to_window()
    refresh()
  }

  private object Transform
  {
    private var _scale: Double = 1.0
    def scale: Double = _scale
    def scale_=(s: Double)
    {
      _scale = (s min 10.0) max 0.1
    }

    def scale_discrete: Double =
    {
      val font_height = GUI.line_metrics(visualizer.metrics.font).getHeight.toInt
      (scale * font_height).floor / font_height
    }

    def apply() =
    {
      val box = visualizer.bounding_box()
      val t = AffineTransform.getScaleInstance(scale_discrete, scale_discrete)
      t.translate(- box.x, - box.y)
      t
    }

    def fit_to_window()
    {
      if (visualizer.visible_graph.is_empty)
        rescale(1.0)
      else {
        val box = visualizer.bounding_box()
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

  visualizer.model.Colors.events += { case _ => painter.repaint() }
  visualizer.model.Mutators.events += { case _ => painter.repaint() }

  private object Mouse_Interaction
  {
    private var draginfo: (Point, List[Graph_Display.Node], List[Layout.Dummy]) =
      (new Point(0, 0), Nil, Nil)

    def pressed(at: Point)
    {
      val c = Transform.pane_to_graph_coordinates(at)
      val l =
        visualizer.find_node(c) match {
          case Some(node) =>
            if (visualizer.Selection.contains(node)) visualizer.Selection.get()
            else List(node)
          case None => Nil
        }
      val d =
        l match {
          case Nil => visualizer.find_dummy(c).toList
          case _ => Nil
        }
      draginfo = (at, l, d)
    }

    def dragged(to: Point)
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
          ds.foreach(d => visualizer.translate_vertex(d, dx / s, dy / s))

        case (ls, _) =>
          ls.foreach(l => visualizer.translate_vertex(Layout.Node(l), dx / s, dy / s))
      }

      draginfo = (to, p, d)
    }

    def clicked(at: Point, m: Key.Modifiers, clicks: Int, right_click: Boolean)
    {
      val c = Transform.pane_to_graph_coordinates(at)

      if (clicks < 2) {
        if (right_click) {
          // FIXME
          if (false) {
            val menu = Popups(graph_panel, visualizer.find_node(c), visualizer.Selection.get())
            menu.show(graph_pane.peer, at.x, at.y)
          }
        }
        else {
          (visualizer.find_node(c), m) match {
            case (Some(node), Key.Modifier.Control) => visualizer.Selection.add(node)
            case (None, Key.Modifier.Control) =>

            case (Some(node), Key.Modifier.Shift) => visualizer.Selection.add(node)
            case (None, Key.Modifier.Shift) =>

            case (Some(node), _) =>
              visualizer.Selection.clear()
              visualizer.Selection.add(node)
            case (None, _) =>
              visualizer.Selection.clear()
          }
        }
      }
    }
  }



  /** controls **/

  private val mutator_dialog =
    new Mutator_Dialog(visualizer, visualizer.model.Mutators, "Filters", "Hide", false)
  private val color_dialog =
    new Mutator_Dialog(visualizer, visualizer.model.Colors, "Colorations")

  private val chooser = new FileChooser {
    fileSelectionMode = FileChooser.SelectionMode.FilesOnly
    title = "Save image (.png or .pdf)"
  }

  private val show_content = new CheckBox() {
    selected = visualizer.show_content
    action = Action("Show content") {
      visualizer.show_content = selected
      visualizer.update_layout()
      refresh()
    }
    tooltip = "Show full node content within graph layout"
  }

  private val show_arrow_heads = new CheckBox() {
    selected = visualizer.show_arrow_heads
    action = Action("Show arrow heads") {
      visualizer.show_arrow_heads = selected
      painter.repaint()
    }
    tooltip = "Draw edges with explicit arrow heads"
  }

  private val show_dummies = new CheckBox() {
    selected = visualizer.show_dummies
    action = Action("Show dummies") {
      visualizer.show_dummies = selected
      painter.repaint()
    }
    tooltip = "Draw dummy nodes within graph layout, for easier mouse dragging"
  }

  private val save_image = new Button {
    action = Action("Save image") {
      chooser.showSaveDialog(this) match {
        case FileChooser.Result.Approve =>
          try { Graph_File.write(chooser.selectedFile, visualizer) }
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
      visualizer.update_layout()
      refresh()
    }
    tooltip = "Regenerate graph layout according to built-in algorithm"
  }

  private val colorations = new Button { action = Action("Colorations") { color_dialog.open } }
  private val filters = new Button { action = Action("Filters") { mutator_dialog.open } }

  private val controls =
    new Wrap_Panel(Wrap_Panel.Alignment.Right)(show_content, show_arrow_heads, show_dummies,
      save_image, zoom, fit_window, update_layout) // FIXME colorations, filters



  /** main layout **/

  layout(graph_pane) = BorderPanel.Position.Center
  layout(controls) = BorderPanel.Position.North

  rescale(1.0)
}
