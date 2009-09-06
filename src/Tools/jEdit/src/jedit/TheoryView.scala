/*
 * jEdit text area as document text source
 *
 * @author Fabian Immler, TU Munich
 * @author Johannes Hölzl, TU Munich
 * @author Makarius
 */

package isabelle.jedit

import scala.actors.Actor, Actor._
import scala.collection.mutable

import isabelle.proofdocument.{ProofDocument, Change, Edit, Insert, Remove}
import isabelle.prover.{Prover, ProverEvents, Command}

import java.awt.{Color, Graphics2D}
import javax.swing.event.{CaretListener, CaretEvent}

import org.gjt.sp.jedit.buffer.{BufferListener, JEditBuffer}
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextAreaExtension, TextAreaPainter}
import org.gjt.sp.jedit.syntax.{ModeProvider, SyntaxStyle}


object TheoryView
{
  
  def choose_color(cmd: Command, doc: ProofDocument): Color = {
    cmd.status(doc) match {
      case Command.Status.UNPROCESSED => new Color(255, 228, 225)
      case Command.Status.FINISHED => new Color(234, 248, 255)
      case Command.Status.FAILED => new Color(255, 192, 192)
      case _ => Color.red
    }
  }
}


class TheoryView(text_area: JEditTextArea)
  extends TextAreaExtension with BufferListener
{
  
  val buffer = text_area.getBuffer

  // start prover
  val prover: Prover = new Prover(Isabelle.system, Isabelle.default_logic(), change_receiver)
  prover.start() // start actor


  /* activation */

  private val phase_overview = new PhaseOverviewPanel(prover, text_area, to_current)

  private val selected_state_controller = new CaretListener {
    override def caretUpdate(e: CaretEvent) = {
      val doc = current_document()
      doc.command_at(e.getDot) match {
        case Some(cmd)
          if (doc.token_start(cmd.tokens.first) <= e.getDot &&
            Isabelle.plugin.selected_state != cmd) =>
          Isabelle.plugin.selected_state = cmd
        case _ =>
      }
    }
  }

  def activate() {
    text_area.addCaretListener(selected_state_controller)
    text_area.addLeftOfScrollBar(phase_overview)
    text_area.getPainter.addExtension(TextAreaPainter.LINE_BACKGROUND_LAYER + 1, this)
    buffer.setTokenMarker(new DynamicTokenMarker(buffer, prover))
    buffer.addBufferListener(this)

    val dockable =
      text_area.getView.getDockableWindowManager.getDockable("isabelle-output")
    if (dockable != null) {
      val output_dockable = dockable.asInstanceOf[OutputDockable]
      val output_text_view = prover.output_text_view
      output_dockable.set_text(output_text_view)
    }

    buffer.propertiesChanged()
  }

  def deactivate() {
    buffer.setTokenMarker(buffer.getMode.getTokenMarker)
    buffer.removeBufferListener(this)
    text_area.getPainter.removeExtension(this)
    text_area.removeLeftOfScrollBar(phase_overview)
    text_area.removeCaretListener(selected_state_controller)
  }


  /* history of changes - TODO: seperate class?*/

  private val change_0 = new Change(prover.document_0.id, None, Nil)
  private var _changes = List(change_0)   // owned by Swing/AWT thread
  def changes = _changes
  private var current_change = change_0

  private def doc_or_pred(c: Change): ProofDocument =
    prover.document(c.id).getOrElse(doc_or_pred(c.parent.get))
  def current_document() = doc_or_pred(current_change)

  /* update to desired version */

  def set_version(goal: Change) {
    // changes in buffer must be ignored
    buffer.removeBufferListener(this)

    def apply(change: Change): Unit = change.edits.foreach {
      case Insert(start, text) => buffer.insert(start, text)
      case Remove(start, text) => buffer.remove(start, text.length)
    }

    def unapply(change: Change): Unit = change.edits.reverse.foreach {
      case Insert(start, text) => buffer.remove(start, text.length)
      case Remove(start, text) => buffer.insert(start, text)
    }

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
    buffer.propertiesChanged()
    invalidate_all()
    phase_overview.repaint()

    // track changes in buffer
    buffer.addBufferListener(this)
  }


  /* sending edits to prover */

  private val edits = new mutable.ListBuffer[Edit]   // owned by Swing/AWT thread

  private val edits_delay = Swing_Thread.delay_last(300) {
    if (!edits.isEmpty) {
      val change = new Change(Isabelle.system.id(), Some(current_change), edits.toList)
      _changes ::= change
      prover ! change
      current_change = change
      edits.clear
    }
  }


  /* BufferListener methods */

  override def preContentInserted(buffer: JEditBuffer,
    start_line: Int, offset: Int, num_lines: Int, length: Int)
  {
    edits += Insert(offset, buffer.getText(offset, length))
    edits_delay()
  }

  override def preContentRemoved(buffer: JEditBuffer,
    start_line: Int, start: Int, num_lines: Int, removed_length: Int)
  {
    edits += Remove(start, buffer.getText(start, removed_length))
    edits_delay()
  }

  override def contentInserted(buffer: JEditBuffer,
    start_line: Int, offset: Int, num_lines: Int, length: Int) { }

  override def contentRemoved(buffer: JEditBuffer,
    start_line: Int, offset: Int, num_lines: Int, length: Int) { }

  override def bufferLoaded(buffer: JEditBuffer) { }
  override def foldHandlerChanged(buffer: JEditBuffer) { }
  override def foldLevelChanged(buffer: JEditBuffer, start_line: Int, end_line: Int) { }
  override def transactionComplete(buffer: JEditBuffer) { }


  /* transforming offsets */

  private def changes_to(doc: ProofDocument): List[Edit] =
    edits.toList ::: List.flatten(current_change.ancestors(_.id == doc.id).map(_.edits))

  def from_current(doc: ProofDocument, offset: Int): Int =
    (offset /: changes_to(doc)) ((i, change) => change before i)

  def to_current(doc: ProofDocument, offset: Int): Int =
    (offset /: changes_to(doc).reverse) ((i, change) => change after i)


  private def lines_of_command(cmd: Command) =
  {
    val document = current_document()
    (buffer.getLineOfOffset(to_current(document, cmd.start(document))),
     buffer.getLineOfOffset(to_current(document, cmd.stop(document))))
  }


  /* (re)painting */

  private val update_delay = Swing_Thread.delay_first(500) { buffer.propertiesChanged() }

  private def update_syntax(cmd: Command) {
    val (line1, line2) = lines_of_command(cmd)
    if (line2 >= text_area.getFirstLine &&
      line1 <= text_area.getFirstLine + text_area.getVisibleLines)
        update_delay()
  }

  private def invalidate_line(cmd: Command) =
  {
    val (start, stop) = lines_of_command(cmd)
    text_area.invalidateLineRange(start, stop)

    if (Isabelle.plugin.selected_state == cmd)
        Isabelle.plugin.selected_state = cmd  // update State view
  }

  private def invalidate_all() =
    text_area.invalidateLineRange(text_area.getFirstPhysicalLine,
      text_area.getLastPhysicalLine)

  private def encolor(gfx: Graphics2D,
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
    var cmd = document.command_at(from_current(start))
    while (cmd.isDefined && cmd.get.start(document) < end) {
      val e = cmd.get
      val begin = start max to_current(e.start(document))
      val finish = (end - 1) min to_current(e.stop(document))
      encolor(gfx, y, metrics.getHeight, begin, finish,
        TheoryView.choose_color(e, document), true)
      cmd = document.commands.next(e)
    }

    gfx.setColor(saved_color)
  }

  override def getToolTipText(x: Int, y: Int): String =
  {
    val document = current_document()
    val offset = from_current(document, text_area.xyToOffset(x, y))
    document.command_at(offset) match {
      case Some(cmd) =>
        document.token_start(cmd.tokens.first)
        cmd.type_at(document, offset - cmd.start(document))
      case None => null
    }
  }


  /* receiving from prover */

  lazy val change_receiver: Actor = actor {
    loop {
      react {
        case ProverEvents.Activate =>   // FIXME !?
          Swing_Thread.now {
            edits.clear
            edits += Insert(0, buffer.getText(0, buffer.getLength))
            edits_delay()
          }
        case c: Command =>
          actor{Isabelle.plugin.command_change.event(c)}
          if(current_document().commands.contains(c))
          Swing_Thread.later {
            // repaint if buffer is active
            if(text_area.getBuffer == buffer) {
              update_syntax(c)
              invalidate_line(c)
              phase_overview.repaint()
            }
          }
        case d: ProofDocument =>
          actor{Isabelle.plugin.document_change.event(d)}
        case x => System.err.println("warning: change_receiver ignored " + x)
      }
    }
  }
}
