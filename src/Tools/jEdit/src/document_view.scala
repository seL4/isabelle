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
import java.awt.event.{MouseMotionAdapter, MouseEvent,
  FocusAdapter, FocusEvent, WindowEvent, WindowAdapter}
import javax.swing.{Popup, PopupFactory, SwingUtilities, BorderFactory}
import javax.swing.event.{CaretListener, CaretEvent}

import org.gjt.sp.util.Log

import org.gjt.sp.jedit.{jEdit, OperatingSystem, Debug}
import org.gjt.sp.jedit.gui.RolloverButton
import org.gjt.sp.jedit.options.GutterOptionPane
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, TextAreaExtension, TextAreaPainter,
  ScrollListener}
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
        val start = text_area.getScreenLineStartOffset(i)
        val stop = text_area.getScreenLineEndOffset(i)
        if start >= 0 && stop >= 0
        val range <- buffer_range.try_restrict(Text.Range(start, stop))
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


  /* snapshot */

  // owned by Swing thread
  @volatile private var was_outdated = false
  @volatile private var was_updated = false

  def update_snapshot(): Document.Snapshot =
  {
    Swing_Thread.require()
    val snapshot = model.snapshot()
    was_updated = was_outdated && !snapshot.is_outdated
    was_outdated = was_outdated || snapshot.is_outdated
    snapshot
  }

  def flush_snapshot(): (Boolean, Document.Snapshot) =
  {
    Swing_Thread.require()
    val snapshot = update_snapshot()
    val updated = was_updated
    if (updated) { was_outdated = false; was_updated = false }
    (updated, snapshot)
  }


  /* HTML popups */

  private var html_popup: Option[Popup] = None

  private def exit_popup() { html_popup.map(_.hide) }

  private val html_panel =
    new HTML_Panel(Isabelle.font_family(), scala.math.round(Isabelle.font_size()))
  html_panel.setBorder(BorderFactory.createLineBorder(Color.black))

  private def html_panel_resize()
  {
    Swing_Thread.now {
      html_panel.resize(Isabelle.font_family(), scala.math.round(Isabelle.font_size()))
    }
  }

  private def init_popup(snapshot: Document.Snapshot, x: Int, y: Int)
  {
    exit_popup()
/* FIXME broken
    val offset = text_area.xyToOffset(x, y)
    val p = new Point(x, y); SwingUtilities.convertPointToScreen(p, text_area.getPainter)

    // FIXME snapshot.cumulate
    snapshot.select_markup(Text.Range(offset, offset + 1))(Isabelle_Rendering.popup) match {
      case Text.Info(_, Some(msg)) #:: _ =>
        val popup = PopupFactory.getSharedInstance().getPopup(text_area, html_panel, p.x, p.y + 60)
        html_panel.render_sync(List(msg))
        Thread.sleep(10)  // FIXME !?
        popup.show
        html_popup = Some(popup)
      case _ =>
    }
*/
  }


  /* subexpression highlighting */

  @volatile private var _highlight_range: Option[Text.Info[Color]] = None
  def highlight_range(): Option[Text.Info[Color]] = _highlight_range

  private var control: Boolean = false

  private def exit_control()
  {
    exit_popup()
    _highlight_range = None
  }

  private val focus_listener = new FocusAdapter {
    override def focusLost(e: FocusEvent) {
      _highlight_range = None // FIXME exit_control !?
    }
  }

  private val window_listener = new WindowAdapter {
    override def windowIconified(e: WindowEvent) { exit_control() }
    override def windowDeactivated(e: WindowEvent) { exit_control() }
  }

  private val mouse_motion_listener = new MouseMotionAdapter {
    override def mouseMoved(e: MouseEvent) {
      control = if (OperatingSystem.isMacOS()) e.isMetaDown else e.isControlDown
      val x = e.getX()
      val y = e.getY()

      if (!model.buffer.isLoaded) exit_control()
      else
        Isabelle.swing_buffer_lock(model.buffer) {
          val snapshot = update_snapshot()

          if (control) init_popup(snapshot, x, y)

          for (Text.Info(range, _) <- _highlight_range) invalidate_range(range)
          _highlight_range =
            if (control) {
              val offset = text_area.xyToOffset(x, y)
              Isabelle_Rendering.subexp(snapshot, Text.Range(offset, offset + 1))
            }
            else None
          for (Text.Info(range, _) <- _highlight_range) invalidate_range(range)
        }
    }
  }


  /* text area painting */

  private val text_area_painter = new Text_Area_Painter(this)

  private val tooltip_painter = new TextAreaExtension
  {
    override def getToolTipText(x: Int, y: Int): String =
    {
      robust_body(null: String) {
        val snapshot = update_snapshot()
        val offset = text_area.xyToOffset(x, y)
        val range = Text.Range(offset, offset + 1)
        val tip =
          if (control) Isabelle_Rendering.tooltip(snapshot, range)
          else Isabelle_Rendering.tooltip_message(snapshot, range)
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
        val gutter = text_area.getGutter
        val width = GutterOptionPane.getSelectionAreaWidth
        val border_width = jEdit.getIntegerProperty("view.gutter.borderWidth", 3)
        val FOLD_MARKER_SIZE = 12

        if (gutter.isSelectionAreaEnabled && !gutter.isExpanded && width >= 12 && line_height >= 12) {
          Isabelle.swing_buffer_lock(model.buffer) {
            val snapshot = update_snapshot()
            for (i <- 0 until physical_lines.length) {
              if (physical_lines(i) != -1) {
                val line_range = proper_line_range(start(i), end(i))

                // gutter icons
                Isabelle_Rendering.gutter_message(snapshot, line_range) match {
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


  /* caret range */

  def caret_range(): Text.Range =
    Isabelle.buffer_lock(model.buffer) {
      def text(i: Text.Offset): Char = model.buffer.getText(i, 1).charAt(0)
      val caret = text_area.getCaretPosition
      try {
        val c = text(caret)
        if (Character.isHighSurrogate(c) && Character.isLowSurrogate(text(caret + 1)))
          Text.Range(caret, caret + 2)
        else if (Character.isLowSurrogate(c) && Character.isHighSurrogate(text(caret - 1)))
          Text.Range(caret - 1, caret + 1)
        else Text.Range(caret, caret + 1)
      }
      catch { case _: ArrayIndexOutOfBoundsException => Text.Range(caret, caret + 1) }
    }


  /* caret handling */

  def selected_command(): Option[Command] =
  {
    Swing_Thread.require()
    update_snapshot().node.command_at(text_area.getCaretPosition).map(_._1)
  }

  private val delay_caret_update =
    Swing_Thread.delay_last(session.input_delay) {
      session.caret_focus.event(Session.Caret_Focus)
    }

  private val caret_listener = new CaretListener {
    override def caretUpdate(e: CaretEvent) { delay_caret_update(true) }
  }


  /* text status overview left of scrollbar */

  private val overview = new Text_Overview(this)
  {
    val delay_repaint =
      Swing_Thread.delay_first(Isabelle.session.update_delay) { repaint() }
  }


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case changed: Session.Commands_Changed =>
          val buffer = model.buffer
          Isabelle.swing_buffer_lock(buffer) {
            val (updated, snapshot) = flush_snapshot()

            if (updated ||
                (changed.nodes.contains(model.name) &&
                 changed.commands.exists(snapshot.node.commands.contains)))
              overview.delay_repaint(true)

            visible_range() match {
              case None =>
              case Some(visible) =>
                if (updated) invalidate_range(visible)
                else {
                  val visible_cmds =
                    snapshot.node.command_range(snapshot.revert(visible)).map(_._1)
                  if (visible_cmds.exists(changed.commands)) {
                    for {
                      line <- 0 until text_area.getVisibleLines
                      val start = text_area.getScreenLineStartOffset(line) if start >= 0
                      val end = text_area.getScreenLineEndOffset(line) if end >= 0
                      val range = proper_line_range(start, end)
                      val line_cmds = snapshot.node.command_range(snapshot.revert(range)).map(_._1)
                      if line_cmds.exists(changed.commands)
                    } text_area.invalidateScreenLineRange(line, line)
                  }
                }
            }
          }

        case Session.Global_Settings => html_panel_resize()

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
    painter.addMouseMotionListener(mouse_motion_listener)
    text_area.addCaretListener(caret_listener)
    text_area.addLeftOfScrollBar(overview)
    session.commands_changed += main_actor
    session.global_settings += main_actor
  }

  private def deactivate()
  {
    val painter = text_area.getPainter
    session.commands_changed -= main_actor
    session.global_settings -= main_actor
    text_area.removeFocusListener(focus_listener)
    text_area.getView.removeWindowListener(window_listener)
    painter.removeMouseMotionListener(mouse_motion_listener)
    text_area.removeCaretListener(caret_listener); delay_caret_update(false)
    text_area.removeLeftOfScrollBar(overview); overview.delay_repaint(false)
    text_area.getGutter.removeExtension(gutter_painter)
    text_area_painter.deactivate()
    painter.removeExtension(tooltip_painter)
    painter.removeExtension(update_perspective)
    exit_popup()
  }
}
