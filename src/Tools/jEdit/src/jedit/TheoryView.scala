/*
 * jEdit text area as document text source
 *
 * @author Fabian Immler, TU Munich
 * @author Johannes Hölzl, TU Munich
 * @author Makarius
 */

package isabelle.jedit

import scala.actors.Actor

import isabelle.proofdocument.Text
import isabelle.prover.{Prover, Command}

import java.awt.Graphics2D
import java.awt.event.{ActionEvent, ActionListener}
import java.awt.Color
import javax.swing.Timer
import javax.swing.event.{CaretListener, CaretEvent}

import org.gjt.sp.jedit.buffer.{BufferListener, JEditBuffer}
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextAreaExtension, TextAreaPainter}
import org.gjt.sp.jedit.syntax.SyntaxStyle


object TheoryView {

  def choose_color(state: Command): Color = {
    if (state == null) Color.red
    else
      state.status match {
        case Command.Status.UNPROCESSED => new Color(255, 228, 225)
        case Command.Status.FINISHED => new Color(234, 248, 255)
        case Command.Status.FAILED => new Color(255, 192, 192)
        case _ => Color.red
      }
  }
}


class TheoryView (text_area: JEditTextArea, document_actor: Actor)
    extends TextAreaExtension with BufferListener {

  private val buffer = text_area.getBuffer
  private val prover = Isabelle.prover_setup(buffer).get.prover
  buffer.addBufferListener(this)


  private var col: Text.Change = null

  private val col_timer = new Timer(300, new ActionListener() {
    override def actionPerformed(e: ActionEvent) = commit
  })

  col_timer.stop
  col_timer.setRepeats(true)


  private val phase_overview = new PhaseOverviewPanel(prover, to_current(_))


  /* activation */

  Isabelle.plugin.font_changed += (_ => update_styles)

  private def update_styles = {
    if (text_area != null) {
      if (Isabelle.plugin.font != null) {
        text_area.getPainter.setStyles(DynamicTokenMarker.reload_styles)
        repaint_all
      }
    }
  }

  private val selected_state_controller = new CaretListener {
    override def caretUpdate(e: CaretEvent) = {
      val cmd = prover.document.find_command_at(e.getDot)
      if (cmd != null && cmd.start <= e.getDot &&
          Isabelle.prover_setup(buffer).get.selected_state != cmd)
        Isabelle.prover_setup(buffer).get.selected_state = cmd
    }
  }

  def activate() = {
    text_area.addCaretListener(selected_state_controller)
    phase_overview.textarea = text_area
    text_area.addLeftOfScrollBar(phase_overview)
    text_area.getPainter.addExtension(TextAreaPainter.LINE_BACKGROUND_LAYER + 1, this)
    buffer.setTokenMarker(new DynamicTokenMarker(buffer, prover.document))
    update_styles
    document_actor ! new Text.Change(0,buffer.getText(0, buffer.getLength),0)
  }

  def deactivate() = {
    text_area.getPainter.removeExtension(this)
    text_area.removeLeftOfScrollBar(phase_overview)
    text_area.removeCaretListener(selected_state_controller)
  }


  /* painting */

  val repaint_delay = new isabelle.utils.Delay(100, () => repaint_all())
  prover.command_info += (_ => repaint_delay.delay_or_ignore())

  def from_current (pos: Int) =
    if (col != null && col.start <= pos)
      if (pos < col.start + col.added.length) col.start
      else pos - col.added.length + col.removed
    else pos

  def to_current (pos : Int) =
    if (col != null && col.start <= pos)
      if (pos < col.start + col.removed) col.start
      else pos + col.added.length - col.removed
    else pos

  def repaint(cmd: Command) =
  {
    if (text_area != null) {
      val start = text_area.getLineOfOffset(to_current(cmd.start))
      val stop = text_area.getLineOfOffset(to_current(cmd.stop) - 1)
      text_area.invalidateLineRange(start, stop)

      if (Isabelle.prover_setup(buffer).get.selected_state == cmd)
        Isabelle.prover_setup(buffer).get.selected_state = cmd  // update State view
    }
  }

  def repaint_all() =
  {
    if (text_area != null)
      text_area.invalidateLineRange(text_area.getFirstPhysicalLine, text_area.getLastPhysicalLine)
  }

  def encolor(gfx: Graphics2D,
    y: Int, height: Int, begin: Int, finish: Int, color: Color, fill: Boolean) =
  {
    val start = text_area.offsetToXY(begin)
    val stop =
      if (finish < buffer.getLength) text_area.offsetToXY(finish)
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


  /* TextAreaExtension methods */

  override def paintValidLine(gfx: Graphics2D,
    screen_line: Int, physical_line: Int, start: Int, end: Int, y: Int) =
  {
    val saved_color = gfx.getColor

    val metrics = text_area.getPainter.getFontMetrics
    var e = prover.document.find_command_at(from_current(start))
    val commands = prover.document.commands.dropWhile(_.stop <= from_current(start)).
      takeWhile(c => to_current(c.start) < end)
    // encolor phase
    for (e <- commands) {
      val begin = start max to_current(e.start)
      val finish = end - 1 min to_current(e.stop)
      encolor(gfx, y, metrics.getHeight, begin, finish, TheoryView.choose_color(e), true)

      // paint details of command
      for (node <- e.root_node.dfs) {
        val begin = to_current(node.start + e.start)
        val finish = to_current(node.stop + e.start)
        if (finish > start && begin < end) {
          encolor(gfx, y + metrics.getHeight - 2, 1, begin max start, finish min end - 1,
            DynamicTokenMarker.choose_color(node.kind), true)
        }
      }
    }

    gfx.setColor(saved_color)
  }

  /* BufferListener methods */

  private def commit {
    if (col != null)
      document_actor ! col
    col = null
    if (col_timer.isRunning())
      col_timer.stop()
  }

  private def delay_commit {
    if (col_timer.isRunning())
      col_timer.restart()
    else
      col_timer.start()
  }


  override def contentInserted(buffer: JEditBuffer,
    start_line: Int, offset: Int, num_lines: Int, length: Int) { }

  override def contentRemoved(buffer: JEditBuffer,
    start_line: Int, offset: Int, num_lines: Int, length: Int) { }

  override def preContentInserted(buffer: JEditBuffer,
    start_line: Int, offset: Int, num_lines: Int, length: Int) =
  {
    val text = buffer.getText(offset, length)
    if (col == null)
      col = new Text.Change(offset, text, 0)
    else if (col.start <= offset && offset <= col.start + col.added.length)
      col = new Text.Change(col.start, col.added + text, col.removed)
    else {
      commit
      col = new Text.Change(offset, text, 0)
    }
    delay_commit
  }

  override def preContentRemoved(buffer: JEditBuffer,
    start_line: Int, start: Int, num_lines: Int, removed: Int) =
  {
    if (col == null)
      col = new Text.Change(start, "", removed)
    else if (col.start > start + removed || start > col.start + col.added.length) {
      commit
      col = new Text.Change(start, "", removed)
    }
    else {
/*      val offset = start - col.start
      val diff = col.added.length - removed
      val (added, add_removed) =
        if (diff < offset)
          (offset max 0, diff - (offset max 0))
        else
          (diff - (offset min 0), offset min 0)
      col = new Text.Changed(start min col.start, added, col.removed - add_removed)*/
      commit
      col = new Text.Change(start, "", removed)
    }
    delay_commit
  }

  override def bufferLoaded(buffer: JEditBuffer) { }
  override def foldHandlerChanged(buffer: JEditBuffer) { }
  override def foldLevelChanged(buffer: JEditBuffer, start_line: Int, end_line: Int) { }
  override def transactionComplete(buffer: JEditBuffer) { }
}
