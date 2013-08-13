/*  Title:      Tools/jEdit/src/pretty_tooltip.scala
    Author:     Makarius

Enhanced tooltip window based on Pretty_Text_Area.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Color, Point, BorderLayout, Dimension}
import java.awt.event.{FocusAdapter, FocusEvent}
import javax.swing.{JWindow, JPanel, JComponent, PopupFactory}
import javax.swing.border.LineBorder

import scala.swing.{FlowPanel, Label}
import scala.swing.event.MouseClicked

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.textarea.TextArea


object Pretty_Tooltip
{
  /* tooltip hierarchy */

  // owned by Swing thread
  private var stack: List[Pretty_Tooltip] = Nil

  private def hierarchy(tip: Pretty_Tooltip): Option[(List[Pretty_Tooltip], List[Pretty_Tooltip])] =
  {
    Swing_Thread.require()

    if (stack.contains(tip)) Some(stack.span(_ != tip))
    else None
  }

  def apply(
    view: View,
    parent: JComponent,
    rendering: Rendering,
    screen_point: Point,
    results: Command.Results,
    info: Text.Info[XML.Body]): Pretty_Tooltip =
  {
    Swing_Thread.require()

    stack match {
      case top :: _ if top.results == results && top.info == info => top
      case _ =>
        val (old, rest) =
          JEdit_Lib.ancestors(parent).collectFirst({ case x: Pretty_Tooltip => x }) match {
            case Some(tip) => hierarchy(tip).getOrElse((stack, Nil))
            case None => (stack, Nil)
          }
        old.foreach(_.hide_popup)

        val tip = new Pretty_Tooltip(view, rendering, parent, screen_point, results, info)
        stack = tip :: rest
        tip.show_popup
        tip
    }
  }


  /* pending event and active state */  // owned by Swing thread

  private var pending: Option[() => Unit] = None
  private var active = true

  private val pending_delay =
    Swing_Thread.delay_last(PIDE.options.seconds("jedit_tooltip_delay")) {
      pending match {
        case Some(body) => pending = None; body()
        case None =>
      }
    }

  def invoke(body: () => Unit): Unit =
    Swing_Thread.require {
      if (active) {
        pending = Some(body)
        pending_delay.invoke()
      }
    }

  def revoke(): Unit =
    Swing_Thread.require {
      pending = None
      pending_delay.revoke()
    }

  private lazy val reactivate_delay =
    Swing_Thread.delay_last(PIDE.options.seconds("jedit_tooltip_delay")) {
      active = true
    }

  private def deactivate(): Unit =
    Swing_Thread.require {
      revoke()
      active = false
      reactivate_delay.invoke()
    }


  /* dismiss */

  def dismiss(tip: Pretty_Tooltip)
  {
    deactivate()
    hierarchy(tip) match {
      case Some((old, _ :: rest)) =>
        old.foreach(_.hide_popup)
        tip.hide_popup
        stack = rest
        rest match {
          case top :: _ => top.request_focus
          case Nil => JEdit_Lib.request_focus_view
        }
      case _ =>
    }
  }

  def dismissed_all(): Boolean =
  {
    deactivate()
    if (stack.isEmpty) false
    else {
      stack.foreach(_.hide_popup)
      stack = Nil
      JEdit_Lib.request_focus_view
      true
    }
  }


  /* auxiliary geometry measurement */

  private lazy val dummy_window = new JWindow

  private def decoration_size(tip: Pretty_Tooltip): (Int, Int) =
  {
    val old_content = dummy_window.getContentPane

    dummy_window.setContentPane(tip)
    dummy_window.pack
    dummy_window.revalidate

    val painter = tip.pretty_text_area.getPainter
    val w = dummy_window.getWidth - painter.getWidth
    val h = dummy_window.getHeight - painter.getHeight

    dummy_window.setContentPane(old_content)

    (w, h)
  }
}


class Pretty_Tooltip private(
  view: View,
  rendering: Rendering,
  parent: JComponent,
  screen_point: Point,
  private val results: Command.Results,
  private val info: Text.Info[XML.Body]) extends JPanel(new BorderLayout)
{
  tip =>

  Swing_Thread.require()


  /* controls */

  private val close = new Label {
    icon = rendering.tooltip_close_icon
    tooltip = "Close tooltip window"
    listenTo(mouse.clicks)
    reactions += { case _: MouseClicked => Pretty_Tooltip.dismiss(tip) }
  }

  private val detach = new Label {
    icon = rendering.tooltip_detach_icon
    tooltip = "Detach tooltip window"
    listenTo(mouse.clicks)
    reactions += {
      case _: MouseClicked =>
        Info_Dockable(view, rendering.snapshot, results, info.info)
        Pretty_Tooltip.dismiss(tip)
    }
  }

  private val controls = new FlowPanel(FlowPanel.Alignment.Left)(close, detach) {
    background = rendering.tooltip_color
  }


  /* text area */

  val pretty_text_area =
    new Pretty_Text_Area(view, () => Pretty_Tooltip.dismiss(tip), true) {
      override def get_background() = Some(rendering.tooltip_color)
    }

  pretty_text_area.addFocusListener(new FocusAdapter {
    override def focusGained(e: FocusEvent)
    {
      tip_border(true)
    }
    override def focusLost(e: FocusEvent)
    {
      Pretty_Tooltip.hierarchy(tip) match {
        case Some((Nil, _)) => Pretty_Tooltip.dismiss(tip)
        case _ => tip_border(false)
      }
    }
  })

  pretty_text_area.resize(Rendering.font_family(),
    Rendering.font_size("jedit_tooltip_font_scale").round)


  /* main content */

  def tip_border(has_focus: Boolean)
  {
    tip.setBorder(new LineBorder(if (has_focus) Color.BLACK else Color.GRAY))
    tip.repaint()
  }
  tip_border(true)

  override def getFocusTraversalKeysEnabled = false
  tip.setBackground(rendering.tooltip_color)
  tip.add(controls.peer, BorderLayout.NORTH)
  tip.add(pretty_text_area)


  /* popup */

  private val popup =
  {
    val screen_bounds = JEdit_Lib.screen_bounds(screen_point)

    val (w, h) =
    {
      val painter = pretty_text_area.getPainter
      val metric = JEdit_Lib.pretty_metric(painter)
      val margin = rendering.tooltip_margin * metric.average

      val formatted = Pretty.formatted(info.info, margin, metric)
      val lines =
        XML.traverse_text(formatted)(0)(
          (n: Int, s: String) => n + s.iterator.filter(_ == '\n').length)

      val (deco_width, deco_height) = Pretty_Tooltip.decoration_size(tip)
      val bounds = rendering.tooltip_bounds

      val h1 = painter.getFontMetrics.getHeight * (lines + 1) + deco_height
      val h2 = (screen_bounds.height * bounds).toInt
      val h = h1 min h2

      val margin1 =
        if (h1 <= h2)
          (0.0 /: split_lines(XML.content(formatted)))({ case (m, line) => m max metric(line) })
        else margin
      val w =
        ((metric.unit * (margin1 + metric.average)).round.toInt + deco_width) min
        (screen_bounds.width * bounds).toInt

      (w, h)
    }

    tip.setSize(new Dimension(w, h))
    tip.setPreferredSize(new Dimension(w, h))

    val x = screen_point.x min (screen_bounds.x + screen_bounds.width - tip.getWidth)
    val y = screen_point.y min (screen_bounds.y + screen_bounds.height - tip.getHeight)
    PopupFactory.getSharedInstance.getPopup(parent, tip, x, y)
  }

  private def show_popup
  {
    popup.show
    pretty_text_area.requestFocus
    pretty_text_area.update(rendering.snapshot, results, info.info)
  }

  private def hide_popup: Unit = popup.hide

  private def request_focus: Unit = pretty_text_area.requestFocus
}

