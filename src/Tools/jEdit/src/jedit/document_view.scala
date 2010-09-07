/*  Title:      Tools/jEdit/src/jedit/document_view.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Document view connected to jEdit text area.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._

import java.awt.event.{MouseAdapter, MouseMotionAdapter, MouseEvent, FocusAdapter, FocusEvent}
import java.awt.{BorderLayout, Graphics, Dimension, Color, Graphics2D}
import javax.swing.{JPanel, ToolTipManager}
import javax.swing.event.{CaretListener, CaretEvent}

import org.gjt.sp.jedit.OperatingSystem
import org.gjt.sp.jedit.gui.RolloverButton
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, TextAreaExtension, TextAreaPainter}
import org.gjt.sp.jedit.syntax.SyntaxStyle


object Document_View
{
  /* physical rendering */

  val outdated_color = new Color(240, 240, 240)
  val unfinished_color = new Color(255, 228, 225)

  val regular_color = new Color(192, 192, 192)
  val warning_color = new Color(255, 165, 0)
  val error_color = new Color(255, 106, 106)
  val bad_color = new Color(255, 204, 153, 100)

  def status_color(snapshot: Document.Snapshot, command: Command): Option[Color] =
  {
    val state = snapshot.state(command)
    if (snapshot.is_outdated) Some(outdated_color)
    else
      Isar_Document.command_status(state.status) match {
        case Isar_Document.Forked(i) if i > 0 => Some(unfinished_color)
        case Isar_Document.Unprocessed => Some(unfinished_color)
        case _ => None
      }
  }

  def overview_color(snapshot: Document.Snapshot, command: Command): Option[Color] =
  {
    val state = snapshot.state(command)
    if (snapshot.is_outdated) None
    else
      Isar_Document.command_status(state.status) match {
        case Isar_Document.Forked(i) if i > 0 => Some(unfinished_color)
        case Isar_Document.Unprocessed => Some(unfinished_color)
        case Isar_Document.Failed => Some(error_color)
        case _ => None
      }
  }


  val message_markup: PartialFunction[Text.Info[Any], Color] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.WRITELN, _), _)) => regular_color
    case Text.Info(_, XML.Elem(Markup(Markup.WARNING, _), _)) => warning_color
    case Text.Info(_, XML.Elem(Markup(Markup.ERROR, _), _)) => error_color
  }

  val background_markup: PartialFunction[Text.Info[Any], Color] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.BAD, _), _)) => bad_color
  }

  val box_markup: PartialFunction[Text.Info[Any], Color] =
  {
    case Text.Info(_, XML.Elem(Markup(Markup.TOKEN_RANGE, _), _)) => regular_color
  }


  /* document view of text area */

  private val key = new Object

  def init(model: Document_Model, text_area: TextArea): Document_View =
  {
    Swing_Thread.require()
    val doc_view = new Document_View(model, text_area)
    text_area.putClientProperty(key, doc_view)
    doc_view.activate()
    doc_view
  }

  def apply(text_area: TextArea): Option[Document_View] =
  {
    Swing_Thread.require()
    text_area.getClientProperty(key) match {
      case doc_view: Document_View => Some(doc_view)
      case _ => None
    }
  }

  def exit(text_area: TextArea)
  {
    Swing_Thread.require()
    apply(text_area) match {
      case None => error("No document view for text area: " + text_area)
      case Some(doc_view) =>
        doc_view.deactivate()
        text_area.putClientProperty(key, null)
    }
  }
}


class Document_View(val model: Document_Model, text_area: TextArea)
{
  private val session = model.session


  /* extended token styles */

  private var styles: Array[SyntaxStyle] = null  // owned by Swing thread

  def extend_styles()
  {
    Swing_Thread.require()
    styles = Document_Model.Token_Markup.extend_styles(text_area.getPainter.getStyles)
  }
  extend_styles()

  def set_styles()
  {
    Swing_Thread.require()
    text_area.getPainter.setStyles(styles)
  }


  /* visible line ranges */

  // simplify slightly odd result of TextArea.getScreenLineEndOffset etc.
  // NB: jEdit already normalizes \r\n and \r to \n
  def proper_line_range(start: Text.Offset, end: Text.Offset): Text.Range =
  {
    val stop = if (start < end) end - 1 else end min model.buffer.getLength
    Text.Range(start, stop)
  }

  def screen_lines_range(): Text.Range =
  {
    val start = text_area.getScreenLineStartOffset(0)
    val raw_end = text_area.getScreenLineEndOffset(text_area.getVisibleLines - 1 max 0)
    proper_line_range(start, if (raw_end >= 0) raw_end else model.buffer.getLength)
  }

  def invalidate_line_range(range: Text.Range)
  {
    text_area.invalidateLineRange(
      model.buffer.getLineOfOffset(range.start),
      model.buffer.getLineOfOffset(range.stop))
  }


  /* commands_changed_actor */

  private val commands_changed_actor = actor {
    loop {
      react {
        case Session.Commands_Changed(changed) =>
          val buffer = model.buffer
          Isabelle.swing_buffer_lock(buffer) {
            val snapshot = model.snapshot()

            if (changed.exists(snapshot.node.commands.contains))
              overview.repaint()

            val visible_range = screen_lines_range()
            val visible_cmds = snapshot.node.command_range(snapshot.revert(visible_range)).map(_._1)
            if (visible_cmds.exists(changed)) {
              for {
                line <- 0 until text_area.getVisibleLines
                val start = text_area.getScreenLineStartOffset(line) if start >= 0
                val end = text_area.getScreenLineEndOffset(line) if end >= 0
                val range = proper_line_range(start, end)
                val line_cmds = snapshot.node.command_range(snapshot.revert(range)).map(_._1)
                if line_cmds.exists(changed)
              } text_area.invalidateScreenLineRange(line, line)

              // FIXME danger of deadlock!?
              // FIXME potentially slow!?
              model.buffer.propertiesChanged()
            }
          }

        case bad => System.err.println("command_change_actor: ignoring bad message " + bad)
      }
    }
  }


  /* subexpression highlighting */

  private def subexp_range(snapshot: Document.Snapshot, x: Int, y: Int): Option[Text.Range] =
  {
    val subexp_markup: PartialFunction[Text.Info[Any], Option[Text.Range]] =
    {
      case Text.Info(range, XML.Elem(Markup(Markup.ML_TYPING, _), _)) =>
        Some(snapshot.convert(range))
    }
    val offset = text_area.xyToOffset(x, y)
    val markup = snapshot.select_markup(Text.Range(offset, offset + 1))(subexp_markup)(None)
    if (markup.hasNext) markup.next.info else None
  }

  private var highlight_range: Option[Text.Range] = None

  private val focus_listener = new FocusAdapter {
    override def focusLost(e: FocusEvent) { highlight_range = None }
  }

  private val mouse_motion_listener = new MouseMotionAdapter {
    override def mouseMoved(e: MouseEvent) {
      val control = if (OperatingSystem.isMacOS()) e.isMetaDown else e.isControlDown
      if (!model.buffer.isLoaded) highlight_range = None
      else
        Isabelle.swing_buffer_lock(model.buffer) {
          highlight_range.map(invalidate_line_range(_))
          highlight_range =
            if (control) subexp_range(model.snapshot(), e.getX(), e.getY()) else None
          highlight_range.map(invalidate_line_range(_))
        }
    }
  }


  /* text_area_extension */

  private val text_area_extension = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int)
    {
      Isabelle.swing_buffer_lock(model.buffer) {
        val snapshot = model.snapshot()
        val saved_color = gfx.getColor
        val ascent = text_area.getPainter.getFontMetrics.getAscent

        try {
          for (i <- 0 until physical_lines.length) {
            if (physical_lines(i) != -1) {
              val line_range = proper_line_range(start(i), end(i))

              // background color: status
              val cmds = snapshot.node.command_range(snapshot.revert(line_range))
              for {
                (command, command_start) <- cmds if !command.is_ignored
                val range = line_range.restrict(snapshot.convert(command.range + command_start))
                r <- Isabelle.gfx_range(text_area, range)
                color <- Document_View.status_color(snapshot, command)
              } {
                gfx.setColor(color)
                gfx.fillRect(r.x, y + i * line_height, r.length, line_height)
              }

              // background color: markup
              for {
                Text.Info(range, color) <-
                  snapshot.select_markup(line_range)(Document_View.background_markup)(null)
                if color != null
                r <- Isabelle.gfx_range(text_area, range)
              } {
                gfx.setColor(color)
                gfx.fillRect(r.x, y + i * line_height, r.length, line_height)
              }

              // subexpression highlighting -- potentially from other snapshot
              if (highlight_range.isDefined) {
                if (line_range.overlaps(highlight_range.get)) {
                  Isabelle.gfx_range(text_area, line_range.restrict(highlight_range.get)) match {
                    case None =>
                    case Some(r) =>
                      gfx.setColor(Color.black)
                      gfx.drawRect(r.x, y + i * line_height, r.length, line_height - 1)
                  }
                }
              }

              // boxed text
              for {
                Text.Info(range, color) <-
                  snapshot.select_markup(line_range)(Document_View.box_markup)(null)
                if color != null
                r <- Isabelle.gfx_range(text_area, range)
              } {
                gfx.setColor(color)
                gfx.drawRect(r.x + 1, y + i * line_height + 1, r.length - 2, line_height - 3)
              }

              // squiggly underline
              for {
                Text.Info(range, color) <-
                  snapshot.select_markup(line_range)(Document_View.message_markup)(null)
                if color != null
                r <- Isabelle.gfx_range(text_area, range)
              } {
                gfx.setColor(color)
                val x0 = (r.x / 2) * 2
                val y0 = r.y + ascent + 1
                for (x1 <- Range(x0, x0 + r.length, 2)) {
                  val y1 = if (x1 % 4 < 2) y0 else y0 + 1
                  gfx.drawLine(x1, y1, x1 + 1, y1)
                }
              }
            }
          }
        }
        finally { gfx.setColor(saved_color) }
      }
    }

    override def getToolTipText(x: Int, y: Int): String =
    {
      Isabelle.swing_buffer_lock(model.buffer) {
        val snapshot = model.snapshot()
        val offset = text_area.xyToOffset(x, y)
        val markup =
          snapshot.select_markup(Text.Range(offset, offset + 1)) {
            case Text.Info(range, XML.Elem(Markup(Markup.ML_TYPING, _), body)) =>
              Isabelle.tooltip(Pretty.string_of(List(Pretty.block(body)), margin = 40))
          } { null }
        if (markup.hasNext) markup.next.info else null
      }
    }
  }


  /* caret handling */

  def selected_command(): Option[Command] =
  {
    Swing_Thread.require()
    model.snapshot().node.proper_command_at(text_area.getCaretPosition)
  }

  private val caret_listener = new CaretListener {
    private val delay = Swing_Thread.delay_last(session.input_delay) {
      session.perspective.event(Session.Perspective)
    }
    override def caretUpdate(e: CaretEvent) { delay() }
  }


  /* overview of command status left of scrollbar */

  private val overview = new JPanel(new BorderLayout)
  {
    private val WIDTH = 10
    private val HEIGHT = 2

    setPreferredSize(new Dimension(WIDTH, 0))

    setRequestFocusEnabled(false)

    addMouseListener(new MouseAdapter {
      override def mousePressed(event: MouseEvent) {
        val line = y_to_line(event.getY)
        if (line >= 0 && line < text_area.getLineCount)
          text_area.setCaretPosition(text_area.getLineStartOffset(line))
      }
    })

    override def addNotify() {
      super.addNotify()
      ToolTipManager.sharedInstance.registerComponent(this)
    }

    override def removeNotify() {
      ToolTipManager.sharedInstance.unregisterComponent(this)
      super.removeNotify
    }

    override def getToolTipText(event: MouseEvent): String =
    {
      val line = y_to_line(event.getY())
      if (line >= 0 && line < text_area.getLineCount) "<html><b>TODO:</b><br>Tooltip</html>"
      else ""
    }

    override def paintComponent(gfx: Graphics)
    {
      super.paintComponent(gfx)
      Swing_Thread.assert()
      val buffer = model.buffer
      Isabelle.buffer_lock(buffer) {
        val snapshot = model.snapshot()
        val saved_color = gfx.getColor  // FIXME needed!?
        try {
          for {
            (command, start) <- snapshot.node.command_starts
            if !command.is_ignored
            val line1 = buffer.getLineOfOffset(snapshot.convert(start))
            val line2 = buffer.getLineOfOffset(snapshot.convert(start + command.length)) + 1
            val y = line_to_y(line1)
            val height = HEIGHT * (line2 - line1)
            color <- Document_View.overview_color(snapshot, command)
          } {
            gfx.setColor(color)
            gfx.fillRect(0, y, getWidth - 1, height)
          }
        }
        finally { gfx.setColor(saved_color) }
      }
    }

    private def line_to_y(line: Int): Int =
      (line * getHeight) / (text_area.getBuffer.getLineCount max text_area.getVisibleLines)

    private def y_to_line(y: Int): Int =
      (y * (text_area.getBuffer.getLineCount max text_area.getVisibleLines)) / getHeight
  }


  /* activation */

  private def activate()
  {
    text_area.getPainter.
      addExtension(TextAreaPainter.LINE_BACKGROUND_LAYER + 1, text_area_extension)
    text_area.addFocusListener(focus_listener)
    text_area.getPainter.addMouseMotionListener(mouse_motion_listener)
    text_area.addCaretListener(caret_listener)
    text_area.addLeftOfScrollBar(overview)
    session.commands_changed += commands_changed_actor
  }

  private def deactivate()
  {
    session.commands_changed -= commands_changed_actor
    text_area.removeFocusListener(focus_listener)
    text_area.getPainter.removeMouseMotionListener(mouse_motion_listener)
    text_area.removeCaretListener(caret_listener)
    text_area.removeLeftOfScrollBar(overview)
    text_area.getPainter.removeExtension(text_area_extension)
  }
}