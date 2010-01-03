/*
 * Document view connected to jEdit text area
 *
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.jedit


import isabelle.proofdocument.{Command, Document, Session}

import scala.actors.Actor._

import java.awt.event.{MouseAdapter, MouseEvent}
import java.awt.{BorderLayout, Graphics, Dimension, Color, Graphics2D}
import javax.swing.{JPanel, ToolTipManager}
import javax.swing.event.{CaretListener, CaretEvent}

import org.gjt.sp.jedit.gui.RolloverButton
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, TextAreaExtension, TextAreaPainter}


object Document_View
{
  def choose_color(command: Command, doc: Document): Color =
  {
    doc.current_state(command).status match {
      case Command.Status.UNPROCESSED => new Color(255, 228, 225)
      case Command.Status.FINISHED => new Color(234, 248, 255)
      case Command.Status.FAILED => new Color(255, 193, 193)
      case _ => Color.red
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


class Document_View(model: Document_Model, text_area: TextArea)
{
  private val session = model.session


  /* visible document -- owned by Swing thread */

  @volatile private var document = model.recent_document()


  /* buffer of changed commands -- owned by Swing thread */

  @volatile private var changed_commands: Set[Command] = Set()

  private val changed_delay = Swing_Thread.delay_first(100) {
    if (!changed_commands.isEmpty) {
      document = model.recent_document()
      for (cmd <- changed_commands if document.commands.contains(cmd)) { // FIXME cover doc states as well!!?
        update_syntax(cmd)
        invalidate_line(cmd)
        overview.repaint()
      }
      changed_commands = Set()
    }
  }


  /* command change actor */

  private case object Exit

  private val command_change_actor = actor {
    loop {
      react {
        case command: Command =>  // FIXME rough filtering according to document family!?
          Swing_Thread.now {
            changed_commands += command
            changed_delay()
          }

        case Exit => reply(()); exit()

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
      def from_current(pos: Int) = model.from_current(document, pos)
      def to_current(pos: Int) = model.to_current(document, pos)
      val saved_color = gfx.getColor

      val metrics = text_area.getPainter.getFontMetrics

      // encolor phase
      var cmd = document.command_at(from_current(start))
      while (cmd.isDefined && cmd.get.start(document) < end) {
        val e = cmd.get
        val begin = start max to_current(e.start(document))
        val finish = (end - 1) min to_current(e.stop(document))
        encolor(gfx, y, metrics.getHeight, begin, finish,
          Document_View.choose_color(e, document), true)
        cmd = document.commands.next(e)
      }

      gfx.setColor(saved_color)
    }

    override def getToolTipText(x: Int, y: Int): String =
    {
      val offset = model.from_current(document, text_area.xyToOffset(x, y))
      document.command_at(offset) match {
        case Some(cmd) =>
          document.token_start(cmd.tokens.first)
          document.current_state(cmd).type_at(offset - cmd.start(document)).getOrElse(null)
        case None => null
      }
    }
  }


  /* caret_listener */

  private var _selected_command: Command = null
  private def selected_command = _selected_command
  private def selected_command_=(cmd: Command)
  {
    _selected_command = cmd
    session.results.event(cmd)
  }

  private val caret_listener = new CaretListener
  {
    override def caretUpdate(e: CaretEvent) {
      document.command_at(e.getDot) match {
        case Some(cmd)
          if (document.token_start(cmd.tokens.first) <= e.getDot &&
            selected_command != cmd) =>
          selected_command = cmd  // FIXME !?
        case _ =>
      }
    }
  }


  /* (re)painting */

  private val update_delay = Swing_Thread.delay_first(500) { model.buffer.propertiesChanged() }

  private def update_syntax(cmd: Command)
  {
    val (line1, line2) = model.lines_of_command(document, cmd)
    if (line2 >= text_area.getFirstLine &&
      line1 <= text_area.getFirstLine + text_area.getVisibleLines)
        update_delay()
  }

  private def invalidate_line(cmd: Command) =
  {
    val (start, stop) = model.lines_of_command(document, cmd)
    text_area.invalidateLineRange(start, stop)

    if (selected_command == cmd)
      session.results.event(cmd)
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

      for (command <- document.commands) {
        val line1 = buffer.getLineOfOffset(model.to_current(document, command.start(document)))
        val line2 = buffer.getLineOfOffset(model.to_current(document, command.stop(document))) + 1
        val y = line_to_y(line1)
        val height = HEIGHT * (line2 - line1)
        gfx.setColor(Document_View.choose_color(command, document))
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
    session.command_change += command_change_actor
  }

  private def deactivate()
  {
    session.command_change -= command_change_actor
    command_change_actor !? Exit
    text_area.removeLeftOfScrollBar(overview)
    text_area.removeCaretListener(caret_listener)
    text_area.getPainter.removeExtension(text_area_extension)
  }
}