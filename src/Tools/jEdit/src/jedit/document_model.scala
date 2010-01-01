/*
 * Document model connected to jEdit buffer
 *
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.jedit


import isabelle.proofdocument.{Change, Command, Edit, Insert, Remove, Document, Session}

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

  private val document_0 = session.begin_document(buffer.getName)

  private val change_0 = new Change(document_0.id, None, Nil, Future.value(document_0, Nil))
  private var _changes = List(change_0)   // owned by Swing thread
  def changes = _changes
  private var current_change = change_0

  private val edits = new mutable.ListBuffer[Edit]   // owned by Swing thread

  private val edits_delay = Swing_Thread.delay_last(300) {
    if (!edits.isEmpty) {
      val new_id = session.create_id()
      val eds = edits.toList
      val change1 = current_change
      val result: Future[Document.Result] = Future.fork {
        val old_doc = change1.document
        Document.text_edits(session, old_doc, new_id, eds)
      }
      val change2 = new Change(new_id, Some(change1), eds, result)
      _changes ::= change2
      session.input(change2)
      current_change = change2
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

  def recent_document(): Document =
  {
    def find(change: Change): Document =
      if (change.result.is_finished || !change.parent.isDefined) change.document
      else find(change.parent.get)
    find(current_change)
  }


  /* transforming offsets */

  private def changes_from(doc: Document): List[Edit] =
    List.flatten(current_change.ancestors(_.id == doc.id).reverse.map(_.edits)) :::
      edits.toList

  def from_current(doc: Document, offset: Int): Int =
    (offset /: changes_from(doc).reverse) ((i, change) => change before i)

  def to_current(doc: Document, offset: Int): Int =
    (offset /: changes_from(doc)) ((i, change) => change after i)

  def lines_of_command(cmd: Command): (Int, Int) =
  {
    val document = recent_document()
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
