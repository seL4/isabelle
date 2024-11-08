/*  Title:      Tools/jEdit/src/pretty_tooltip.scala
    Author:     Makarius

Tooltip based on Pretty_Text_Area.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Color, Point, BorderLayout, Dimension}
import java.awt.event.{FocusAdapter, FocusEvent}
import javax.swing.{JPanel, JComponent, SwingUtilities, JLayeredPane}
import javax.swing.border.LineBorder

import scala.swing.{FlowPanel, Label}
import scala.swing.event.MouseClicked

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.textarea.TextArea


object Pretty_Tooltip {
  /* tooltip hierarchy */

  // owned by GUI thread
  private var stack: List[Pretty_Tooltip] = Nil

  private def hierarchy(
    pretty_tooltip: Pretty_Tooltip
  ): Option[(List[Pretty_Tooltip], List[Pretty_Tooltip])] = {
    GUI_Thread.require {}

    if (stack.contains(pretty_tooltip)) Some(stack.span(_ != pretty_tooltip))
    else None
  }

  private def descendant(parent: JComponent): Option[Pretty_Tooltip] =
    GUI_Thread.require {
      stack.find(pretty_tooltip => pretty_tooltip.original_parent == parent)
    }

  def apply(
    view: View,
    parent: JComponent,
    location: Point,
    rendering: JEdit_Rendering,
    results: Command.Results,
    output: List[XML.Elem]
  ): Unit = {
    GUI_Thread.require {}

    stack match {
      case top :: _ if top.results == results && top.output == output =>
      case _ =>
        GUI.layered_pane(parent) match {
          case None =>
          case Some(layered) =>
            val (old, rest) =
              GUI.ancestors(parent).collectFirst({ case x: Pretty_Tooltip => x }) match {
                case Some(pretty_tooltip) => hierarchy(pretty_tooltip).getOrElse((stack, Nil))
                case None => (stack, Nil)
              }
            old.foreach(_.hide_popup())

            val loc = SwingUtilities.convertPoint(parent, location, layered)
            val pretty_tooltip =
              new Pretty_Tooltip(view, layered, parent, loc, rendering, results, output)
            stack = pretty_tooltip :: rest
            pretty_tooltip.show_popup()
        }
    }
  }


  /* pending event and active state */  // owned by GUI thread

  private var pending: Option[() => Unit] = None
  private var active = true

  private val pending_delay =
    Delay.last(PIDE.options.seconds("jedit_tooltip_delay"), gui = true) {
      pending match {
        case Some(body) => pending = None; body()
        case None =>
      }
    }

  def invoke(body: () => Unit): Unit =
    GUI_Thread.require {
      if (active) {
        pending = Some(body)
        pending_delay.invoke()
      }
    }

  def revoke(): Unit =
    GUI_Thread.require {
      pending = None
      pending_delay.revoke()
    }

  private lazy val reactivate_delay =
    Delay.last(PIDE.options.seconds("jedit_tooltip_delay"), gui = true) {
      active = true
    }

  private def deactivate(): Unit =
    GUI_Thread.require {
      revoke()
      active = false
      reactivate_delay.invoke()
    }


  /* dismiss */

  private lazy val focus_delay =
    Delay.last(PIDE.session.input_delay, gui = true) { dismiss_unfocused() }

  def dismiss_unfocused(): Unit = {
    stack.span(pretty_tooltip => !pretty_tooltip.pretty_text_area.isFocusOwner) match {
      case (Nil, _) =>
      case (unfocused, rest) =>
        deactivate()
        unfocused.foreach(_.hide_popup())
        stack = rest
    }
  }

  def dismiss(pretty_tooltip: Pretty_Tooltip): Unit = {
    deactivate()
    hierarchy(pretty_tooltip) match {
      case Some((old, _ :: rest)) =>
        rest match {
          case top :: _ => top.request_focus()
          case Nil => JEdit_Lib.request_focus_view()
        }
        old.foreach(_.hide_popup())
        pretty_tooltip.hide_popup()
        stack = rest
      case _ =>
    }
  }

  def dismiss_descendant(parent: JComponent): Unit =
    descendant(parent).foreach(dismiss)

  def dismissed_all(): Boolean = {
    deactivate()
    if (stack.isEmpty) false
    else {
      JEdit_Lib.request_focus_view()
      stack.foreach(_.hide_popup())
      stack = Nil
      true
    }
  }
}


class Pretty_Tooltip private(
  view: View,
  layered: JLayeredPane,
  val original_parent: JComponent,
  location: Point,
  rendering: JEdit_Rendering,
  private val results: Command.Results,
  private val output: List[XML.Elem]
) extends JPanel(new BorderLayout) {
  pretty_tooltip =>

  GUI_Thread.require {}


  /* controls */

  private val close = new Label {
    icon = rendering.tooltip_close_icon
    tooltip = "Close tooltip window"
    listenTo(mouse.clicks)
    reactions += { case _: MouseClicked => Pretty_Tooltip.dismiss(pretty_tooltip) }
  }

  private val detach = new Label {
    icon = rendering.tooltip_detach_icon
    tooltip = "Detach tooltip window"
    listenTo(mouse.clicks)
    reactions += {
      case _: MouseClicked =>
        Info_Dockable(view, rendering.snapshot, results, output)
        Pretty_Tooltip.dismiss(pretty_tooltip)
    }
  }

  private val controls = new FlowPanel(FlowPanel.Alignment.Left)(close, detach) {
    background = rendering.tooltip_color
  }


  /* text area */

  val pretty_text_area: Pretty_Text_Area =
    new Pretty_Text_Area(view, () => Pretty_Tooltip.dismiss(pretty_tooltip), true) {
      override def get_background(): Option[Color] = Some(rendering.tooltip_color)
    }

  pretty_text_area.addFocusListener(new FocusAdapter {
    override def focusGained(e: FocusEvent): Unit = {
      tip_border(true)
      Pretty_Tooltip.focus_delay.invoke()
    }
    override def focusLost(e: FocusEvent): Unit = {
      tip_border(false)
      Pretty_Tooltip.focus_delay.invoke()
    }
  })

  pretty_text_area.resize(Font_Info.main(PIDE.options.real("jedit_popup_font_scale")))


  /* main content */

  def tip_border(has_focus: Boolean): Unit = {
    pretty_tooltip.setBorder(new LineBorder(if (has_focus) Color.BLACK else Color.GRAY))
    pretty_tooltip.repaint()
  }
  tip_border(true)

  override def getFocusTraversalKeysEnabled = false
  pretty_tooltip.setBackground(rendering.tooltip_color)
  pretty_tooltip.add(controls.peer, BorderLayout.NORTH)
  pretty_tooltip.add(pretty_text_area)


  /* popup */

  private val popup: Popup = {
    val screen = GUI.screen_location(layered, location)
    val size = {
      val bounds = JEdit_Rendering.popup_bounds

      val w_max = layered.getWidth min (screen.bounds.width * bounds).toInt
      val h_max = layered.getHeight min (screen.bounds.height * bounds).toInt

      val painter = pretty_text_area.getPainter
      val geometry = JEdit_Lib.window_geometry(pretty_tooltip, painter)
      val metric = JEdit_Lib.font_metric(painter)
      val margin =
        metric.pretty_margin(rendering.tooltip_margin,
          limit = ((w_max - geometry.deco_width) / metric.average_width).toInt)

      val formatted = Pretty.formatted(Pretty.separate(output), margin = margin, metric = metric)
      val lines = XML.content_lines(formatted)

      val h = painter.getLineHeight * lines + geometry.deco_height
      val margin1 =
        if (h <= h_max) {
          split_lines(XML.content(formatted)).foldLeft(0.0) { case (m, line) => m max metric(line) }
        }
        else margin.toDouble
      val w = (metric.unit * (margin1 + metric.average)).round.toInt + geometry.deco_width

      new Dimension(w min w_max, h min h_max)
    }
    new Popup(layered, pretty_tooltip, screen.relative(layered, size), size)
  }

  private def show_popup(): Unit = {
    popup.show
    pretty_text_area.requestFocus()
    pretty_text_area.update(rendering.snapshot, results, output)
  }

  private def hide_popup(): Unit = popup.hide

  private def request_focus(): Unit = pretty_text_area.requestFocus()
}

