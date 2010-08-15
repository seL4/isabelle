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
  def choose_color(snapshot: Document.Snapshot, command: Command): Color =
  {
    val state = snapshot.state(command)
    if (snapshot.is_outdated) new Color(240, 240, 240)
    else
      Toplevel.command_status(state.status) match {
        case Toplevel.Forked(i) if i > 0 => new Color(255, 228, 225)
        case Toplevel.Finished => new Color(234, 248, 255)
        case Toplevel.Failed => new Color(255, 193, 193)
        case Toplevel.Unprocessed => new Color(255, 228, 225)
        case _ => Color.red
      }
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


  /* commands_changed_actor */

  private val commands_changed_actor = actor {
    loop {
      react {
        case Session.Commands_Changed(changed) =>
          Swing_Thread.now {
            // FIXME cover doc states as well!!?
            val snapshot = model.snapshot()
            if (changed.exists(snapshot.node.commands.contains))
              full_repaint(snapshot, changed)
          }

        case bad => System.err.println("command_change_actor: ignoring bad message " + bad)
      }
    }
  }

  def full_repaint(snapshot: Document.Snapshot, changed: Set[Command])
  {
    Swing_Thread.require()

    val buffer = model.buffer
    var visible_change = false

    for ((command, start) <- snapshot.node.command_starts) {
      if (changed(command)) {
        val stop = start + command.length
        val line1 = buffer.getLineOfOffset(snapshot.convert(start))
        val line2 = buffer.getLineOfOffset(snapshot.convert(stop))
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
      Swing_Thread.assert()

      val snapshot = model.snapshot()

      val command_range: Iterable[(Command, Text.Offset)] =
      {
        val range = snapshot.node.command_range(snapshot.revert(start(0)))
        if (range.hasNext) {
          val (cmd0, start0) = range.next
          new Iterable[(Command, Text.Offset)] {
            def iterator =
              Document.Node.command_starts(snapshot.node.commands.iterator(cmd0), start0)
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

            val a = snapshot.revert(line_start)
            val b = snapshot.revert(line_end)
            val cmds = command_range.iterator.
              dropWhile { case (cmd, c) => c + cmd.length <= a } .
              takeWhile { case (_, c) => c < b }

            for ((command, command_start) <- cmds if !command.is_ignored) {
              val p =
                text_area.offsetToXY(line_start max snapshot.convert(command_start))
              val q =
                text_area.offsetToXY(line_end min snapshot.convert(command_start + command.length))
              assert(p.y == q.y)
              gfx.setColor(Document_View.choose_color(snapshot, command))
              gfx.fillRect(p.x, y, q.x - p.x, line_height)
            }
          }
          y += line_height
        }
      }
      finally { gfx.setColor(saved_color) }
    }

    override def getToolTipText(x: Int, y: Int): String =
    {
      Swing_Thread.assert()

      val snapshot = model.snapshot()
      val offset = snapshot.revert(text_area.xyToOffset(x, y))
      snapshot.node.command_at(offset) match {
        case Some((command, command_start)) =>
          snapshot.state(command).type_at(offset - command_start) match {
            case Some(text) => Isabelle.tooltip(text)
            case None => null
          }
        case None => null
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
      val buffer = model.buffer
      val snapshot = model.snapshot()
      val saved_color = gfx.getColor  // FIXME needed!?
      try {
        for ((command, start) <- snapshot.node.command_starts if !command.is_ignored) {
          val line1 = buffer.getLineOfOffset(snapshot.convert(start))
          val line2 = buffer.getLineOfOffset(snapshot.convert(start + command.length)) + 1
          val y = line_to_y(line1)
          val height = HEIGHT * (line2 - line1)
          gfx.setColor(Document_View.choose_color(snapshot, command))
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