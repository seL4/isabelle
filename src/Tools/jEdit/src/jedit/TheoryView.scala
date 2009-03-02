/*
 * jEdit text area as document text source
 *
 * @author Fabian Immler, TU Munich
 * @author Johannes Hölzl, TU Munich
 * @author Makarius
 */

package isabelle.jedit


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

  def choose_color(markup: String): Color = {
    // TODO: as properties
    markup match {
      // logical entities
      case Markup.TCLASS | Markup.TYCON | Markup.FIXED_DECL | Markup.FIXED | Markup.CONST_DECL
        | Markup.CONST | Markup.FACT_DECL | Markup.FACT | Markup.DYNAMIC_FACT
        | Markup.LOCAL_FACT_DECL | Markup.LOCAL_FACT => new Color(255, 0, 255)
      // inner syntax
      case Markup.TFREE | Markup.FREE => Color.blue
      case Markup.TVAR | Markup.SKOLEM | Markup.BOUND | Markup.VAR => Color.green
      case Markup.NUM | Markup.FLOAT | Markup.XNUM | Markup.XSTR | Markup.LITERAL
        | Markup.INNER_COMMENT => new Color(255, 128, 128)
      case Markup.SORT | Markup.TYP | Markup.TERM | Markup.PROP
        | Markup.ATTRIBUTE | Markup.METHOD => Color.yellow
      // embedded source text
      case Markup.ML_SOURCE | Markup.DOC_SOURCE | Markup.ANTIQ | Markup.ML_ANTIQ
        | Markup.DOC_ANTIQ => new Color(0, 192, 0)
      // outer syntax
      case Markup.IDENT | Markup.COMMAND | Markup.KEYWORD => Color.blue
      case Markup.VERBATIM => Color.green
      case Markup.COMMENT => Color.gray
      case Markup.CONTROL => Color.white
      case Markup.MALFORMED => Color.red
      case Markup.STRING | Markup.ALTSTRING => Color.orange
      // other
      case _ => Color.white
    }
  }
}


class TheoryView (text_area: JEditTextArea)
    extends TextAreaExtension with Text with BufferListener {

  private val buffer = text_area.getBuffer
  private val prover = Isabelle.prover_setup(buffer).get.prover
  buffer.addBufferListener(this)


  private var col: Text.Changed = null

  private val col_timer = new Timer(300, new ActionListener() {
    override def actionPerformed(e: ActionEvent) = commit()
  })

  col_timer.stop
  col_timer.setRepeats(true)


  private val phase_overview = new PhaseOverviewPanel(prover)


  /* activation */

  Isabelle.plugin.font_changed += (_ => update_font())

  private def update_font() = {
    if (text_area != null) {
      if (Isabelle.plugin.font != null) {
        val painter = text_area.getPainter
        painter.setStyles(painter.getStyles.map(style =>
          new SyntaxStyle(style.getForegroundColor, style.getBackgroundColor, Isabelle.plugin.font)
        ))
        painter.setFont(Isabelle.plugin.font)
        repaint_all()
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
    update_font()
  }

  def deactivate() = {
    text_area.getPainter.removeExtension(this)
    text_area.removeLeftOfScrollBar(phase_overview)
    text_area.removeCaretListener(selected_state_controller)
  }


  /* painting */

  val repaint_delay = new isabelle.utils.Delay(100, () => repaint_all())
  prover.command_info += (_ => repaint_delay.delay_or_ignore())

  private def from_current(pos: Int) =
    if (col != null && col.start <= pos)
      if (pos < col.start + col.added) col.start
      else pos - col.added + col.removed
    else pos

  private def to_current(pos : Int) =
    if (col != null && col.start <= pos)
      if (pos < col.start + col.removed) col.start
      else pos + col.added - col.removed
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
        p.x = p.x + text_area.getPainter.getFontMetrics.charWidth(' ')
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

    // encolor phase
    while (e != null && to_current(e.start) < end) {
      val begin = start max to_current(e.start)
      val finish = end - 1 min to_current(e.stop)
      encolor(gfx, y, metrics.getHeight, begin, finish, TheoryView.choose_color(e), true)

      // paint details of command
      for (node <- e.root_node.dfs) {
        val begin = to_current(node.start + e.start)
        val finish = to_current(node.end + e.start)
        if (finish > start && begin < end) {
          encolor(gfx, y + metrics.getHeight - 4, 2, begin max start, finish min end,
            TheoryView.choose_color(node.short), true)
        }
      }
      e = e.next
    }

    gfx.setColor(saved_color)
  }


  /* Text methods */

  def content(start: Int, stop: Int) = buffer.getText(start, stop - start)
  def length = buffer.getLength
  val changes = new EventBus[Text.Changed]


  /* BufferListener methods */

  private def commit() {
    if (col != null)
      changes.event(col)
    col = null
    if (col_timer.isRunning())
      col_timer.stop()
  }

  private def delay_commit() {
    if (col_timer.isRunning())
      col_timer.restart()
    else
      col_timer.start()
  }


  override def contentInserted(buffer: JEditBuffer,
    start_line: Int, offset: Int, num_lines: Int, length: Int)
  {
/*
    if (col == null)
      col = new Text.Changed(offset, length, 0)
    else if (col.start <= offset && offset <= col.start + col.added)
      col = new Text.Changed(col.start, col.added + length, col.removed)
    else {
      commit()
      col = new Text.Changed(offset, length, 0)
    }
    delay_commit()
*/
    changes.event(new Text.Changed(offset, length, 0))
  }

  override def preContentRemoved(buffer: JEditBuffer,
    start_line: Int, start: Int, num_lines: Int, removed: Int) =
  {
/*
    if (col == null)
      col = new Text.Changed(start, 0, removed)
    else if (col.start > start + removed || start > col.start + col.added) {
      commit()
      col = new Text.Changed(start, 0, removed)
    }
    else {
      val offset = start - col.start
      val diff = col.added - removed
      val (added, add_removed) =
        if (diff < offset)
          (offset max 0, diff - (offset max 0))
        else
          (diff - (offset min 0), offset min 0)
      col = new Text.Changed(start min col.start, added, col.removed - add_removed)
    }
    delay_commit()
*/
    changes.event(new Text.Changed(start, 0, removed))
  }

  override def contentRemoved(buffer: JEditBuffer,
    start_line: Int, offset: Int, num_lines: Int, length: Int) { }
  override def preContentInserted(buffer: JEditBuffer,
    start_line: Int, offset: Int, num_lines: Int, length: Int) { }
  override def bufferLoaded(buffer: JEditBuffer) { }
  override def foldHandlerChanged(buffer: JEditBuffer) { }
  override def foldLevelChanged(buffer: JEditBuffer, start_line: Int, end_line: Int) { }
  override def transactionComplete(buffer: JEditBuffer) { }
}
