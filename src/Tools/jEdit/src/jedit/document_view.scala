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
import org.gjt.sp.jedit.syntax.SyntaxStyle


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


  /* extended token styles */

  private var styles: Array[SyntaxStyle] = null  // owned by Swing thread

  def extend_styles()
  {
    Swing_Thread.assert()
    styles = Isabelle_Token_Marker.extend_styles(text_area.getPainter.getStyles)
  }
  extend_styles()

  def set_styles()
  {
    Swing_Thread.assert()
    text_area.getPainter.setStyles(styles)
  }


  /* commands_changed_actor */

  private val commands_changed_actor = actor {
    loop {
      react {
        case Command_Set(changed) =>
          Swing_Thread.now {
            // FIXME cover doc states as well!!?
            val document = model.recent_document()
            if (changed.exists(document.commands.contains))
              full_repaint(document, changed)
          }

        case bad => System.err.println("command_change_actor: ignoring bad message " + bad)
      }
    }
  }

  def full_repaint(document: Document, changed: Set[Command])
  {
    Swing_Thread.assert()

    val buffer = model.buffer
    var visible_change = false

    for ((command, start) <- document.command_starts) {
      if (changed(command)) {
        val stop = start + command.length
        val line1 = buffer.getLineOfOffset(model.to_current(document, start))
        val line2 = buffer.getLineOfOffset(model.to_current(document, stop))
        if (line2 >= text_area.getFirstLine &&
            line1 <= text_area.getFirstLine + text_area.getVisibleLines)
          visible_change = true
        text_area.invalidateLineRange(line1, line2)
      }
    }
    if (visible_change) model.buffer.propertiesChanged()

    overview.repaint()  // FIXME paint here!?
  }


  /* text_area_extension */

  private val text_area_extension = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y0: Int, line_height: Int)
    {
      Swing_Thread.now {
        val document = model.recent_document()
        def from_current(pos: Int) = model.from_current(document, pos)
        def to_current(pos: Int) = model.to_current(document, pos)

        val command_range: Iterable[(Command, Int)] =
        {
          val range = document.command_range(from_current(start(0)))
          if (range.hasNext) {
            val (cmd0, start0) = range.next
            new Iterable[(Command, Int)] {
              def iterator = Document.command_starts(document.commands.iterator(cmd0), start0)
            }
          }
          else Iterable.empty
        }

        val saved_color = gfx.getColor
        try {
          var y = y0
          for (i <- 0 until physical_lines.length) {
            if (physical_lines(i) != -1) {
              val line_start = start(i)
              val line_end = model.visible_line_end(line_start, end(i))

              val a = from_current(line_start)
              val b = from_current(line_end)
              val cmds = command_range.iterator.
                dropWhile { case (cmd, c) => c + cmd.length <= a } .
                takeWhile { case (_, c) => c < b }

              for ((command, command_start) <- cmds if !command.is_ignored) {
                val p = text_area.offsetToXY(line_start max to_current(command_start))
                val q = text_area.offsetToXY(line_end min to_current(command_start + command.length))
                assert(p.y == q.y)
                gfx.setColor(Document_View.choose_color(document, command))
                gfx.fillRect(p.x, y, q.x - p.x, line_height)
              }
            }
            y += line_height
          }
        }
        finally { gfx.setColor(saved_color) }
      }
    }

    override def getToolTipText(x: Int, y: Int): String =
    {
      val document = model.recent_document()
      val offset = model.from_current(document, text_area.xyToOffset(x, y))
      document.command_at(offset) match {
        case Some((command, command_start)) =>
          document.current_state(command).type_at(offset - command_start) match {
            case Some(text) => Isabelle.tooltip(text)
            case None => null
          }
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
      def to_current(pos: Int) = model.to_current(document, pos)
      val saved_color = gfx.getColor  // FIXME needed!?
      try {
        for ((command, start) <- document.command_starts if !command.is_ignored) {
          val line1 = buffer.getLineOfOffset(to_current(start))
          val line2 = buffer.getLineOfOffset(to_current(start + command.length)) + 1
          val y = line_to_y(line1)
          val height = HEIGHT * (line2 - line1)
          gfx.setColor(Document_View.choose_color(document, command))
          gfx.fillRect(0, y, getWidth - 1, height)
        }
      }
      finally { gfx.setColor(saved_color) }
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