/*  Title:      Tools/jEdit/src/pretty_tooltip.scala
    Author:     Makarius

Enhanced tooltip window based on Pretty_Text_Area.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Color, Point, BorderLayout, Window, Dimension}
import java.awt.event.{WindowEvent, WindowAdapter, KeyEvent, KeyAdapter, KeyListener}
import javax.swing.{SwingUtilities, JDialog, JPanel, JComponent}
import javax.swing.border.LineBorder

import scala.swing.{FlowPanel, Label}
import scala.swing.event.MouseClicked

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.textarea.TextArea


object Pretty_Tooltip
{
  /* window stack -- owned by Swing thread */

  private var window_stack: List[Pretty_Tooltip] = Nil

  def windows(): List[Pretty_Tooltip] =
  {
    Swing_Thread.require()
    window_stack
  }

  def apply(
    view: View,
    parent: JComponent,
    rendering: Rendering,
    mouse_x: Int, mouse_y: Int,
    results: Command.Results,
    range: Text.Range,
    body: XML.Body): Pretty_Tooltip =
  {
    Swing_Thread.require()

    val old_windows =
      JEdit_Lib.parent_window(parent) match {
        case Some(parent_window: Pretty_Tooltip) =>
          windows().find(_ == parent_window) match {
            case Some(window) => window.descendants()
            case None => windows()
          }
        case _ => windows()
      }

    val window =
      old_windows.reverse match {
        case Nil =>
          val window = new Pretty_Tooltip(view)
          window_stack = window :: window_stack
          window
        case window :: others =>
          others.foreach(_.dispose)
          window
      }
    window.init(rendering, parent, mouse_x, mouse_y, results, range, body)
    window
  }


  /* global dismissed delay -- owned by Swing thread */

  private var active = true

  private lazy val reactivate_delay =
    Swing_Thread.delay_last(PIDE.options.seconds("jedit_tooltip_delay")) {
      active = true
    }

  def dismissed
  {
    Swing_Thread.require()
    active = false
    reactivate_delay.invoke()
  }

  def is_active: Boolean =
  {
    Swing_Thread.require()
    active
  }
}


class Pretty_Tooltip private(view: View) extends JDialog
{
  window =>

  Swing_Thread.require()


  /* implicit state -- owned by Swing thread */

  private var current_rendering: Rendering =
    Rendering(Document.State.init.snapshot(), PIDE.options.value)
  private var current_results = Command.Results.empty
  private var current_range = Text.Range(-1)
  private var current_body: XML.Body = Nil


  /* window hierarchy */

  def descendants(): List[Pretty_Tooltip] =
    if (Pretty_Tooltip.windows().exists(_ == window))
      Pretty_Tooltip.windows().takeWhile(_ != window)
    else Nil

  window.addWindowFocusListener(new WindowAdapter {
    override def windowLostFocus(e: WindowEvent) {
      if (!descendants().exists(_.isDisplayable))
        window.dismiss
    }
  })


  /* main content */

  window.setUndecorated(true)
  window.getRootPane.setBorder(new LineBorder(Color.BLACK))

  private val content_panel =
    new JPanel(new BorderLayout) { override def getFocusTraversalKeysEnabled = false }
  window.setContentPane(content_panel)

  val pretty_text_area = new Pretty_Text_Area(view, () => window.dismiss, true) {
    override def get_background() = Some(current_rendering.tooltip_color)
  }
  window.add(pretty_text_area)


  /* controls */

  private val close = new Label {
    icon = current_rendering.tooltip_close_icon
    tooltip = "Close tooltip window"
    listenTo(mouse.clicks)
    reactions += { case _: MouseClicked => window.dismiss }
  }

  private val detach = new Label {
    icon = current_rendering.tooltip_detach_icon
    tooltip = "Detach tooltip window"
    listenTo(mouse.clicks)
    reactions += {
      case _: MouseClicked =>
        Info_Dockable(view, current_rendering.snapshot, current_results, current_body)
        window.dismiss
    }
  }

  private val controls = new FlowPanel(FlowPanel.Alignment.Left)(close, detach)
  window.add(controls.peer, BorderLayout.NORTH)


  /* init */

  def init(
    rendering: Rendering,
    parent: JComponent,
    mouse_x: Int, mouse_y: Int,
    results: Command.Results,
    range: Text.Range,
    body: XML.Body)
  {
    if (!(results == current_results && range == current_range && body == current_body)) {
      current_rendering = rendering
      current_results = results
      current_range = range
      current_body = body

      pretty_text_area.resize(Rendering.font_family(),
        Rendering.font_size("jedit_tooltip_font_scale").round)
      pretty_text_area.update(rendering.snapshot, results, body)

      content_panel.setBackground(rendering.tooltip_color)
      controls.background = rendering.tooltip_color


      /* window geometry */

      val screen_point = new Point(mouse_x, mouse_y)
      SwingUtilities.convertPointToScreen(screen_point, parent)
      val screen_bounds = JEdit_Lib.screen_bounds(screen_point)

      {
        val painter = pretty_text_area.getPainter
        val metric = JEdit_Lib.pretty_metric(painter)
        val margin = rendering.tooltip_margin * metric.average
        val lines =
          XML.traverse_text(Pretty.formatted(body, margin, metric))(0)(
            (n: Int, s: String) => n + s.iterator.filter(_ == '\n').length)

        if (window.getWidth == 0) {
          window.setSize(new Dimension(100, 100))
          window.setPreferredSize(new Dimension(100, 100))
        }
        window.pack
        window.revalidate

        val deco_width = window.getWidth - painter.getWidth
        val deco_height = window.getHeight - painter.getHeight

        val bounds = rendering.tooltip_bounds
        val w =
          ((metric.unit * (margin + metric.average)).round.toInt + deco_width) min
          (screen_bounds.width * bounds).toInt
        val h =
          (painter.getFontMetrics.getHeight * (lines + 1) + deco_height) min
          (screen_bounds.height * bounds).toInt

        window.setSize(new Dimension(w, h))
        window.setPreferredSize(new Dimension(w, h))
        window.pack
        window.revalidate

        val x = screen_point.x min (screen_bounds.x + screen_bounds.width - window.getWidth)
        val y = screen_point.y min (screen_bounds.y + screen_bounds.height - window.getHeight)
        window.setLocation(x, y)
      }
    }

    window.setVisible(true)
    pretty_text_area.requestFocus
    pretty_text_area.refresh()
  }


  /* dismiss */

  def dismiss
  {
    Swing_Thread.require()
    Pretty_Tooltip.dismissed
    window.dispose
  }
}

