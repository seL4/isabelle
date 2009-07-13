/*
 * jEdit text area as document text source
 *
 * @author Fabian Immler, TU Munich
 * @author Johannes Hölzl, TU Munich
 * @author Makarius
 */

package isabelle.jedit

import scala.actors.Actor
import scala.actors.Actor._

import isabelle.proofdocument.{ProofDocument, Text}
import isabelle.prover.{Prover, ProverEvents, Command}

import java.awt.Graphics2D
import java.awt.event.{ActionEvent, ActionListener}
import java.awt.Color
import javax.swing.Timer
import javax.swing.event.{CaretListener, CaretEvent}

import org.gjt.sp.jedit.buffer.{BufferListener, JEditBuffer}
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextAreaExtension, TextAreaPainter}
import org.gjt.sp.jedit.syntax.{ModeProvider, SyntaxStyle}


object TheoryView
{

  val MAX_CHANGE_LENGTH = 1500
  
  def choose_color(cmd: Command, doc: ProofDocument): Color = {
    cmd.status(doc) match {
      case Command.Status.UNPROCESSED => new Color(255, 228, 225)
      case Command.Status.FINISHED => new Color(234, 248, 255)
      case Command.Status.FAILED => new Color(255, 192, 192)
      case _ => Color.red
    }
  }
}


class TheoryView (text_area: JEditTextArea, document_actor: Actor)
    extends TextAreaExtension with BufferListener
{

  def id() = Isabelle.system.id()
  
  private val buffer = text_area.getBuffer
  private val prover = Isabelle.prover_setup(buffer).get.prover


  private var col: Text.Change = null
  private val col_timer = new Timer(300, new ActionListener() {
    override def actionPerformed(e: ActionEvent) = commit
  })

  col_timer.stop
  col_timer.setRepeats(true)


  private val phase_overview = new PhaseOverviewPanel(prover, text_area, to_current)


  /* activation */

  private val selected_state_controller = new CaretListener {
    override def caretUpdate(e: CaretEvent) = {
      val doc = current_document()
      val cmd = doc.find_command_at(e.getDot)
      if (cmd != null && doc.token_start(cmd.tokens.first) <= e.getDot &&
          Isabelle.prover_setup(buffer).get.selected_state != cmd)
        Isabelle.prover_setup(buffer).get.selected_state = cmd
    }
  }

  def activate() {
    text_area.addCaretListener(selected_state_controller)
    text_area.addLeftOfScrollBar(phase_overview)
    text_area.getPainter.addExtension(TextAreaPainter.LINE_BACKGROUND_LAYER + 1, this)
    buffer.setTokenMarker(new DynamicTokenMarker(buffer, prover))
    buffer.addBufferListener(this)

    col = Text.Change(Some(current_change), Isabelle.system.id(), 0,
      buffer.getText(0, buffer.getLength), "")
    commit
  }

  def deactivate() {
    buffer.setTokenMarker(buffer.getMode.getTokenMarker)
    buffer.removeBufferListener(this)
    text_area.getPainter.removeExtension(this)
    text_area.removeLeftOfScrollBar(phase_overview)
    text_area.removeCaretListener(selected_state_controller)
  }


  /* painting */

  val update_delay = Swing_Thread.delay(500){ buffer.propertiesChanged() }
  val repaint_delay = Swing_Thread.delay(100){ repaint_all() }
  
  val change_receiver = actor {
    loop {
      react {
        case ProverEvents.Activate =>
          activate()
        case c: Command =>
          update_delay()
          repaint_delay()
          phase_overview.repaint_delay()
        case x => System.err.println("warning: change_receiver ignored " + x)
      }
    }
  }


  def transform_back(from: Text.Change, to: Text.Change, pos: Int): Int =
    if (from.id == to.id) pos
    else {
      val shifted =
        if (from.start <= pos)
          if (pos < from.start + from.added.length) from.start
          else pos - from.added.length + from.removed.length
        else pos
      transform_back(from.base.get, to, shifted)
    }

  def transform_forward(from: Text.Change, to: Text.Change, pos: Int): Int = 
    if (from.id == to.id) pos
    else {
      val shifted = transform_forward(from, to.base.get, pos)
      if (to.start <= shifted) {
        if (shifted < to.start + to.removed.length) to.start
        else shifted + to.added.length - to.removed.length
      } else shifted
    }
  
  def from_current(doc: ProofDocument, pos: Int) = {
    val from = if (col == null) current_change else col
    val to = changes.find(_.id == doc.id).get
    transform_back(from, to, pos)
  }
  def to_current(doc: ProofDocument, pos: Int) = {
    val from = changes.find(_.id == doc.id).get
    val to = if (col == null) current_change else col
    transform_forward(from, to, pos)
  }

  def repaint(cmd: Command) =
  {
    val document = current_document()
    if (text_area != null) {
      val start = text_area.getLineOfOffset(to_current(document, cmd.start(document)))
      val stop = text_area.getLineOfOffset(to_current(document, cmd.stop(document)) - 1)
      text_area.invalidateLineRange(start, stop)

      if (Isabelle.prover_setup(buffer).get.selected_state == cmd)
        Isabelle.prover_setup(buffer).get.selected_state = cmd  // update State view
    }
  }

  def repaint_all()
  {
    if (text_area != null)
      text_area.invalidateLineRange(text_area.getFirstPhysicalLine, text_area.getLastPhysicalLine)
  }

  def encolor(gfx: Graphics2D,
    y: Int, height: Int, begin: Int, finish: Int, color: Color, fill: Boolean)
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
    screen_line: Int, physical_line: Int, start: Int, end: Int, y: Int)
  {
    val document = current_document()
    def from_current(pos: Int) = this.from_current(document, pos)
    def to_current(pos: Int) = this.to_current(document, pos)
    val saved_color = gfx.getColor

    val metrics = text_area.getPainter.getFontMetrics

    // encolor phase
    var e = document.find_command_at(from_current(start))
    while (e != null && e.start(document) < end) {
      val begin = start max to_current(e.start(document))
      val finish = end - 1 min to_current(e.stop(document))
      encolor(gfx, y, metrics.getHeight, begin, finish,
        TheoryView.choose_color(e, document), true)
      e = document.commands.next(e).getOrElse(null)
    }

    gfx.setColor(saved_color)
  }

  override def getToolTipText(x: Int, y: Int) = {
    val document = current_document()
    val offset = from_current(document, text_area.xyToOffset(x, y))
    val cmd = document.find_command_at(offset)
    if (cmd != null) {
      document.token_start(cmd.tokens.first)
      cmd.type_at(document, offset - cmd.start(document))
    } else null
  }

  /* history of changes - TODO: seperate class?*/

  val change_0 = Text.Change(None, prover.document_0.id, 0, "", "")
  private var changes = List(change_0)
  private var current_change = change_0
  def get_changes = changes
  
  private def doc_or_pred(c: Text.Change): ProofDocument =
    prover.document(c.id).getOrElse(doc_or_pred(c.base.get))
  def current_document() = doc_or_pred(current_change)

  /* update to desired version */

  def set_version(goal: Text.Change) {
    // changes in buffer must be ignored
    buffer.removeBufferListener(this)

    def apply(c: Text.Change) = {
        buffer.remove(c.start, c.removed.length)
        buffer.insert(c.start, c.added)}
    def unapply(c: Text.Change) = {
      buffer.remove(c.start, c.added.length)
      buffer.insert(c.start, c.removed)}

    // undo/redo changes
    val ancs_current = current_change.ancestors
    val ancs_goal = goal.ancestors
    val paired = ancs_current.reverse zip ancs_goal.reverse
    def last_common[A](xs: List[(A, A)]): Option[A] = {
      xs match {
        case (x, y) :: xs =>
          if (x == y)
            xs match {
              case (a, b) :: ys =>
                if (a == b) last_common(xs)
                else Some(x)
              case _ => Some(x)
            }
          else None
        case _ => None
      }
    }
    val common_anc = last_common(paired).get

    ancs_current.takeWhile(_ != common_anc) map unapply
    ancs_goal.takeWhile(_ != common_anc).reverse map apply

    current_change = goal
    // invoke repaint
    update_delay()
    repaint_delay()
    phase_overview.repaint_delay()

    //track changes in buffer
    buffer.addBufferListener(this)
  }

  /* BufferListener methods */

  private def commit: Unit = synchronized {
    if (col != null) {
      def split_changes(c: Text.Change): List[Text.Change] = {
        val MAX = TheoryView.MAX_CHANGE_LENGTH
        if (c.added.length <= MAX) List(c)
        else Text.Change(c.base, c.id, c.start, c.added.substring(0, MAX), c.removed) ::
          split_changes(Text.Change(Some(c), id(), c.start + MAX, c.added.substring(MAX), ""))
      }
      val new_changes = split_changes(col)
      changes ++= new_changes
      new_changes map (document_actor ! _)
      current_change = new_changes.last
    }
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
    start_line: Int, offset: Int, num_lines: Int, length: Int)
  {
    val text = buffer.getText(offset, length)
    if (col == null)
      col = new Text.Change(Some(current_change), id(), offset, text, "")
    else if (col.start <= offset && offset <= col.start + col.added.length)
      col = new Text.Change(Some(current_change), col.id,
              col.start, col.added + text, col.removed)
    else {
      commit
      col = new Text.Change(Some(current_change), id(), offset, text, "")
    }
    delay_commit
  }

  override def preContentRemoved(buffer: JEditBuffer,
    start_line: Int, start: Int, num_lines: Int, removed_length: Int)
  {
    val removed = buffer.getText(start, removed_length)
    if (col == null)
      col = new Text.Change(Some(current_change), id(), start, "", removed)
    else if (col.start > start + removed_length || start > col.start + col.added.length) {
      commit
      col = new Text.Change(Some(current_change), id(), start, "", removed)
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
      col = new Text.Change(Some(current_change), id(), start, "", removed)
    }
    delay_commit
  }

  override def bufferLoaded(buffer: JEditBuffer) { }
  override def foldHandlerChanged(buffer: JEditBuffer) { }
  override def foldLevelChanged(buffer: JEditBuffer, start_line: Int, end_line: Int) { }
  override def transactionComplete(buffer: JEditBuffer) { }

}
