/*
 * Document model connected to jEdit buffer
 *
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.jedit


import isabelle.proofdocument.{Change, Command, Edit, Insert, Remove, Proof_Document, Session}

import scala.actors.Actor, Actor._
import scala.collection.mutable

import org.gjt.sp.jedit.Buffer
import org.gjt.sp.jedit.buffer.{BufferAdapter, BufferListener, JEditBuffer}
import org.gjt.sp.jedit.syntax.{ModeProvider, SyntaxStyle}


object Document_Model
{
  /* document model of buffer */

  private val key = "isabelle.document_model"

  def init(session: Session, buffer: Buffer): Document_Model =
  {
    Swing_Thread.assert()
    val model = new Document_Model(session, buffer)
    buffer.setProperty(key, model)
    model.activate()
    model
  }

  def apply(buffer: Buffer): Option[Document_Model] =
  {
    Swing_Thread.assert()
    buffer.getProperty(key) match {
      case model: Document_Model => Some(model)
      case _ => None
    }
  }

  def exit(buffer: Buffer)
  {
    Swing_Thread.assert()
    apply(buffer) match {
      case None => error("No document model for buffer: " + buffer)
      case Some(model) =>
        model.deactivate()
        buffer.unsetProperty(key)
    }
  }
}

class Document_Model(val session: Session, val buffer: Buffer)
{
  /* changes vs. edits */

  private val change_0 = new Change(Isabelle.session.document_0.id, None, Nil)  // FIXME !?
  private var _changes = List(change_0)   // owned by Swing/AWT thread
  def changes = _changes
  private var current_change = change_0

  private val edits = new mutable.ListBuffer[Edit]   // owned by Swing thread

  private val edits_delay = Swing_Thread.delay_last(300) {
    if (!edits.isEmpty) {
      val change = new Change(session.create_id(), Some(current_change), edits.toList)
      _changes ::= change
      session.input(change)
      current_change = change
      edits.clear
    }
  }


  /* buffer listener */

  private val buffer_listener: BufferListener = new BufferAdapter
  {
    override def contentInserted(buffer: JEditBuffer,
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
  }


  /* history of changes */

  private def doc_or_pred(c: Change): Proof_Document =
    session.document(c.id).getOrElse(doc_or_pred(c.parent.get))

  def current_document() = doc_or_pred(current_change)


  /* update to desired version */

  def set_version(goal: Change)
  {
    // changes in buffer must be ignored
    buffer.removeBufferListener(buffer_listener)

    def apply(change: Change): Unit =
      change.edits.foreach {
        case Insert(start, text) => buffer.insert(start, text)
        case Remove(start, text) => buffer.remove(start, text.length)
      }

    def unapply(change: Change): Unit =
      change.edits.reverse.foreach {
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
    // invalidate_all()  FIXME
    // overview.repaint()  FIXME

    // track changes in buffer
    buffer.addBufferListener(buffer_listener)
  }


  /* transforming offsets */

  private def changes_from(doc: Proof_Document): List[Edit] =
    List.flatten(current_change.ancestors(_.id == doc.id).reverse.map(_.edits)) :::
      edits.toList

  def from_current(doc: Proof_Document, offset: Int): Int =
    (offset /: changes_from(doc).reverse) ((i, change) => change before i)

  def to_current(doc: Proof_Document, offset: Int): Int =
    (offset /: changes_from(doc)) ((i, change) => change after i)

  def lines_of_command(cmd: Command): (Int, Int) =
  {
    val document = current_document()
    (buffer.getLineOfOffset(to_current(document, cmd.start(document))),
     buffer.getLineOfOffset(to_current(document, cmd.stop(document))))
  }


  /* activation */

  def activate()
  {
    buffer.setTokenMarker(new Isabelle_Token_Marker(this))  // FIXME tune!?
    buffer.addBufferListener(buffer_listener)
    buffer.propertiesChanged()

    edits += Insert(0, buffer.getText(0, buffer.getLength))
    edits_delay()
  }

  def deactivate()
  {
    buffer.setTokenMarker(buffer.getMode.getTokenMarker)
    buffer.removeBufferListener(buffer_listener)
  }
}
