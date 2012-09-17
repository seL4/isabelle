/*  Title:      Tools/jEdit/src/document_view.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Document view connected to jEdit text area.
*/

package isabelle.jedit


import isabelle._

import scala.collection.mutable
import scala.collection.immutable.SortedMap
import scala.actors.Actor._

import java.lang.System
import java.text.BreakIterator
import java.awt.{Color, Graphics2D, Point}
import java.awt.event.{MouseMotionAdapter, MouseAdapter, MouseEvent,
  FocusAdapter, FocusEvent, WindowEvent, WindowAdapter}
import javax.swing.event.{CaretListener, CaretEvent}

import org.gjt.sp.util.Log

import org.gjt.sp.jedit.{jEdit, OperatingSystem, Debug}
import org.gjt.sp.jedit.gui.RolloverButton
import org.gjt.sp.jedit.options.GutterOptionPane
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, TextAreaExtension, TextAreaPainter}
import org.gjt.sp.jedit.syntax.{SyntaxStyle}


object Document_View
{
  /* document view of text area */

  private val key = new Object

  def apply(text_area: JEditTextArea): Option[Document_View] =
  {
    Swing_Thread.require()
    text_area.getClientProperty(key) match {
      case doc_view: Document_View => Some(doc_view)
      case _ => None
    }
  }

  def exit(text_area: JEditTextArea)
  {
    Swing_Thread.require()
    apply(text_area) match {
      case None =>
      case Some(doc_view) =>
        doc_view.deactivate()
        text_area.putClientProperty(key, null)
    }
  }

  def init(model: Document_Model, text_area: JEditTextArea): Document_View =
  {
    exit(text_area)
    val doc_view = new Document_View(model, text_area)
    text_area.putClientProperty(key, doc_view)
    doc_view.activate()
    doc_view
  }
}


class Document_View(val model: Document_Model, val text_area: JEditTextArea)
{
  private val session = model.session


  /* robust extension body */

  def robust_body[A](default: A)(body: => A): A =
  {
    try {
      Swing_Thread.require()
      if (model.buffer == text_area.getBuffer) body
      else {
        Log.log(Log.ERROR, this, ERROR("Inconsistent document model"))
        default
      }
    }
    catch { case t: Throwable => Log.log(Log.ERROR, this, t); default }
  }


  /* visible text range */

  // NB: TextArea.getScreenLineEndOffset of last line is beyond Buffer.getLength
  def proper_line_range(start: Text.Offset, end: Text.Offset): Text.Range =
    Text.Range(start, end min model.buffer.getLength)

  def visible_range(): Option[Text.Range] =
  {
    val n = text_area.getVisibleLines
    if (n > 0) {
      val start = text_area.getScreenLineStartOffset(0)
      val raw_end = text_area.getScreenLineEndOffset(n - 1)
      Some(proper_line_range(start, if (raw_end >= 0) raw_end else model.buffer.getLength))
    }
    else None
  }

  def invalidate_range(range: Text.Range)
  {
    text_area.invalidateLineRange(
      model.buffer.getLineOfOffset(range.start),
      model.buffer.getLineOfOffset(range.stop))
  }


  /* perspective */

  def perspective(): Text.Perspective =
  {
    Swing_Thread.require()
    val buffer_range = model.buffer_range()
    Text.Perspective(
      for {
        i <- 0 until text_area.getVisibleLines
        start = text_area.getScreenLineStartOffset(i)
        stop = text_area.getScreenLineEndOffset(i)
        if start >= 0 && stop >= 0
        range <- buffer_range.try_restrict(Text.Range(start, stop))
        if !range.is_singularity
      }
      yield range)
  }

  private def update_perspective = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int)
    {
      model.update_perspective()
    }
  }


  /* active areas within the text */

  private class Active_Area[A](
    rendering: Isabelle_Rendering => Text.Range => Option[Text.Info[A]])
  {
    private var the_info: Option[Text.Info[A]] = None

    def info: Option[Text.Info[A]] = the_info

    def update(new_info: Option[Text.Info[A]])
    {
      val old_info = the_info
      if (new_info != old_info) {
        for { opt <- List(old_info, new_info); Text.Info(range, _) <- opt }
          invalidate_range(range)
        the_info = new_info
      }
    }

    def update_rendering(r: Isabelle_Rendering, range: Text.Range)
    { update(rendering(r)(range)) }

    def reset { update(None) }
  }

  // owned by Swing thread

  private var control: Boolean = false

  private val highlight_area = new Active_Area[Color]((r: Isabelle_Rendering) => r.highlight _)
  def highlight_info(): Option[Text.Info[Color]] = highlight_area.info

  private val hyperlink_area = new Active_Area[Hyperlink]((r: Isabelle_Rendering) => r.hyperlink _)
  def hyperlink_info(): Option[Text.Info[Hyperlink]] = hyperlink_area.info

  private val active_areas = List(highlight_area, hyperlink_area)
  private def active_reset(): Unit = active_areas.foreach(_.reset)

  private val focus_listener = new FocusAdapter {
    override def focusLost(e: FocusEvent) { active_reset() }
  }

  private val window_listener = new WindowAdapter {
    override def windowIconified(e: WindowEvent) { active_reset() }
    override def windowDeactivated(e: WindowEvent) { active_reset() }
  }

  private val mouse_listener = new MouseAdapter {
    override def mouseClicked(e: MouseEvent) {
      hyperlink_area.info match {
        case Some(Text.Info(range, link)) => link.follow(text_area.getView)
        case None =>
      }
    }
  }

  private val mouse_motion_listener = new MouseMotionAdapter {
    override def mouseMoved(e: MouseEvent) {
      control = if (OperatingSystem.isMacOS()) e.isMetaDown else e.isControlDown
      if (control && model.buffer.isLoaded) {
        JEdit_Lib.buffer_lock(model.buffer) {
          val rendering = Isabelle_Rendering(model.snapshot(), Isabelle.options.value)
          val mouse_range = model.point_range(text_area.xyToOffset(e.getX(), e.getY()))
          active_areas.foreach(_.update_rendering(rendering, mouse_range))
        }
      }
      else active_reset()
    }
  }


  /* text area painting */

  private val text_area_painter = new Text_Area_Painter(this)

  private val tooltip_painter = new TextAreaExtension
  {
    override def getToolTipText(x: Int, y: Int): String =
    {
      robust_body(null: String) {
        val rendering = Isabelle_Rendering(model.snapshot(), Isabelle.options.value)
        val offset = text_area.xyToOffset(x, y)
        val range = Text.Range(offset, offset + 1)
        val tip =
          if (control) rendering.tooltip(range)
          else rendering.tooltip_message(range)
        tip.map(Isabelle.tooltip(_)) getOrElse null
      }
    }
  }

  private val gutter_painter = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int)
    {
      robust_body(()) {
        Swing_Thread.assert()

        val gutter = text_area.getGutter
        val width = GutterOptionPane.getSelectionAreaWidth
        val border_width = jEdit.getIntegerProperty("view.gutter.borderWidth", 3)
        val FOLD_MARKER_SIZE = 12

        if (gutter.isSelectionAreaEnabled && !gutter.isExpanded && width >= 12 && line_height >= 12) {
          JEdit_Lib.buffer_lock(model.buffer) {
            val rendering = Isabelle_Rendering(model.snapshot(), Isabelle.options.value)

            for (i <- 0 until physical_lines.length) {
              if (physical_lines(i) != -1) {
                val line_range = proper_line_range(start(i), end(i))

                // gutter icons
                rendering.gutter_message(line_range) match {
                  case Some(icon) =>
                    val x0 = (FOLD_MARKER_SIZE + width - border_width - icon.getIconWidth) max 10
                    val y0 = y + i * line_height + (((line_height - icon.getIconHeight) / 2) max 0)
                    icon.paintIcon(gutter, gfx, x0, y0)
                  case None =>
                }
              }
            }
          }
        }
      }
    }
  }


  /* caret handling */

  private val delay_caret_update =
    Swing_Thread.delay_last(Time.seconds(Isabelle.options.real("editor_input_delay"))) {
      session.caret_focus.event(Session.Caret_Focus)
    }

  private val caret_listener = new CaretListener {
    override def caretUpdate(e: CaretEvent) { delay_caret_update.invoke() }
  }


  /* text status overview left of scrollbar */

  private object overview extends Text_Overview(this)
  {
    val delay_repaint =
      Swing_Thread.delay_first(
        Time.seconds(Isabelle.options.real("editor_update_delay"))) { repaint() }
  }


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case _: Session.Raw_Edits =>
          Swing_Thread.later {
            overview.delay_repaint.postpone(
              Time.seconds(Isabelle.options.real("editor_input_delay")))
          }

        case changed: Session.Commands_Changed =>
          val buffer = model.buffer
          Swing_Thread.later {
            JEdit_Lib.buffer_lock(buffer) {
              if (model.buffer == text_area.getBuffer) {
                val snapshot = model.snapshot()

                if (changed.assignment ||
                    (changed.nodes.contains(model.name) &&
                     changed.commands.exists(snapshot.node.commands.contains)))
                  Swing_Thread.later { overview.delay_repaint.invoke() }

                visible_range() match {
                  case Some(visible) =>
                    if (changed.assignment) invalidate_range(visible)
                    else {
                      val visible_cmds =
                        snapshot.node.command_range(snapshot.revert(visible)).map(_._1)
                      if (visible_cmds.exists(changed.commands)) {
                        for {
                          line <- 0 until text_area.getVisibleLines
                          start = text_area.getScreenLineStartOffset(line) if start >= 0
                          end = text_area.getScreenLineEndOffset(line) if end >= 0
                          range = proper_line_range(start, end)
                          line_cmds = snapshot.node.command_range(snapshot.revert(range)).map(_._1)
                          if line_cmds.exists(changed.commands)
                        } text_area.invalidateScreenLineRange(line, line)
                      }
                    }
                  case None =>
                }
              }
            }
          }

        case bad => System.err.println("command_change_actor: ignoring bad message " + bad)
      }
    }
  }


  /* activation */

  private def activate()
  {
    val painter = text_area.getPainter
    painter.addExtension(TextAreaPainter.LOWEST_LAYER, update_perspective)
    painter.addExtension(TextAreaPainter.LINE_BACKGROUND_LAYER + 1, tooltip_painter)
    text_area_painter.activate()
    text_area.getGutter.addExtension(gutter_painter)
    text_area.addFocusListener(focus_listener)
    text_area.getView.addWindowListener(window_listener)
    painter.addMouseListener(mouse_listener)
    painter.addMouseMotionListener(mouse_motion_listener)
    text_area.addCaretListener(caret_listener)
    text_area.addLeftOfScrollBar(overview)
    session.raw_edits += main_actor
    session.commands_changed += main_actor
  }

  private def deactivate()
  {
    val painter = text_area.getPainter
    session.raw_edits -= main_actor
    session.commands_changed -= main_actor
    text_area.removeFocusListener(focus_listener)
    text_area.getView.removeWindowListener(window_listener)
    painter.removeMouseMotionListener(mouse_motion_listener)
    painter.removeMouseListener(mouse_listener)
    text_area.removeCaretListener(caret_listener); delay_caret_update.revoke()
    text_area.removeLeftOfScrollBar(overview); overview.delay_repaint.revoke()
    text_area.getGutter.removeExtension(gutter_painter)
    text_area_painter.deactivate()
    painter.removeExtension(tooltip_painter)
    painter.removeExtension(update_perspective)
  }
}
