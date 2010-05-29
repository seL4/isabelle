/*  Title:      Tools/jEdit/src/jedit/document_view.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Document view connected to jEdit text area.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._

import java.awt.event.{MouseAdapter, MouseEvent}
import java.awt.{BorderLayout, Graphics, Dimension, Color, Graphics2D}
import javax.swing.{JPanel, ToolTipManager}
import javax.swing.event.{CaretListener, CaretEvent}

import org.gjt.sp.jedit.gui.RolloverButton
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, TextAreaExtension, TextAreaPainter}


object Document_View
{
  def choose_color(document: Document, command: Command): Color =
  {
    val state = document.current_state(command)
    if (state.forks > 0) new Color(255, 228, 225)
    else if (state.forks < 0) Color.red
    else
      state.status match {
        case Command.Status.UNPROCESSED => new Color(255, 228, 225)
        case Command.Status.FINISHED => new Color(234, 248, 255)
        case Command.Status.FAILED => new Color(255, 193, 193)
        case Command.Status.UNDEFINED => Color.red
      }
  }


  /* document view of text area */

  private val key = new Object

  def init(model: Document_Model, text_area: TextArea): Document_View =
  {
    Swing_Thread.assert()
    val doc_view = new Document_View(model, text_area)
    text_area.putClientProperty(key, doc_view)
    doc_view.activate()
    doc_view
  }

  def apply(text_area: TextArea): Option[Document_View] =
  {
    Swing_Thread.assert()
    text_area.getClientProperty(key) match {
      case doc_view: Document_View => Some(doc_view)
      case _ => None
    }
  }

  def exit(text_area: TextArea)
  {
    Swing_Thread.assert()
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


  /* commands_changed_actor */

  private val commands_changed_actor = actor {
    loop {
      react {
        case Command_Set(changed) =>
          Swing_Thread.now {
            val document = model.recent_document()
            // FIXME cover doc states as well!!?
            for (command <- changed if document.commands.contains(command)) {
              update_syntax(document, command)
              invalidate_line(document, command)
              overview.repaint()
            }
          }

        case bad => System.err.println("command_change_actor: ignoring bad message " + bad)
      }
    }
  }


  /* text_area_extension */

  private val text_area_extension = new TextAreaExtension
  {
    override def paintValidLine(gfx: Graphics2D,
      screen_line: Int, physical_line: Int, start: Int, end: Int, y: Int)
    {
      val document = model.recent_document()
      def from_current(pos: Int) = model.from_current(document, pos)
      def to_current(pos: Int) = model.to_current(document, pos)
      val metrics = text_area.getPainter.getFontMetrics
      val saved_color = gfx.getColor
      try {
        for ((command, command_start) <-
          document.command_range(from_current(start), from_current(end)))
        {
          val begin = start max to_current(command_start)
          val finish = (end - 1) min to_current(command_start + command.length)
          encolor(gfx, y, metrics.getHeight, begin, finish,
            Document_View.choose_color(document, command), true)
        }
      }
      finally { gfx.setColor(saved_color) }
    }

    override def getToolTipText(x: Int, y: Int): String =
    {
      val document = model.recent_document()
      val offset = model.from_current(document, text_area.xyToOffset(x, y))
      document.command_at(offset) match {
        case Some((command, command_start)) =>
          document.current_state(command).type_at(offset - command_start) getOrElse null
        case None => null
      }
    }
  }


  /* caret handling */

  def selected_command: Option[Command] =
    model.recent_document().command_at(text_area.getCaretPosition) match {
      case Some((command, _)) => Some(command)
      case None => None
    }

  private val caret_listener = new CaretListener
  {
    private var last_selected_command: Option[Command] = None
    override def caretUpdate(e: CaretEvent)
    {
      val selected = selected_command
      if (selected != last_selected_command) {
        last_selected_command = selected
        if (selected.isDefined) session.indicate_command_change(selected.get)
      }
    }
  }


  /* (re)painting */

  private val update_delay = Swing_Thread.delay_first(500) { model.buffer.propertiesChanged() }
  // FIXME update_delay property

  private def update_syntax(document: Document, cmd: Command)
  {
    val (line1, line2) = model.lines_of_command(document, cmd)
    if (line2 >= text_area.getFirstLine &&
      line1 <= text_area.getFirstLine + text_area.getVisibleLines)
        update_delay()
  }

  private def invalidate_line(document: Document, cmd: Command) =
  {
    val (start, stop) = model.lines_of_command(document, cmd)
    text_area.invalidateLineRange(start, stop)
  }

  private def invalidate_all() =
    text_area.invalidateLineRange(text_area.getFirstPhysicalLine,
      text_area.getLastPhysicalLine)

  private def encolor(gfx: Graphics2D,
    y: Int, height: Int, begin: Int, finish: Int, color: Color, fill: Boolean)
  {
    val start = text_area.offsetToXY(begin)
    val stop =
      if (finish < model.buffer.getLength) text_area.offsetToXY(finish)
      else {
        val p = text_area.offsetToXY(finish - 1)
        val metrics = text_area.getPainter.getFontMetrics
        p.x = p.x + (metrics.charWidth(' ') max metrics.getMaxAdvance)
        p
      }

    if (start != null && stop != null) {
      gfx.setColor(color)
      if (fill) gfx.fillRect(start.x, y, stop.x - start.x, height)
      else gfx.drawRect(start.x, y, stop.x - start.x, height)
    }
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
      val buffer = model.buffer
      val document = model.recent_document()

      for ((command, start) <- document.command_range(0)) {
        val line1 = buffer.getLineOfOffset(model.to_current(document, start))
        val line2 = buffer.getLineOfOffset(model.to_current(document, start + command.length)) + 1
        val y = line_to_y(line1)
        val height = HEIGHT * (line2 - line1)
        gfx.setColor(Document_View.choose_color(document, command))
        gfx.fillRect(0, y, getWidth - 1, height)
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
    text_area.addCaretListener(caret_listener)
    text_area.addLeftOfScrollBar(overview)
    session.commands_changed += commands_changed_actor
  }

  private def deactivate()
  {
    session.commands_changed -= commands_changed_actor
    text_area.removeLeftOfScrollBar(overview)
    text_area.removeCaretListener(caret_listener)
    text_area.getPainter.removeExtension(text_area_extension)
  }
}