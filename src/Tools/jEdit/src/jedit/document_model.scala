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
  /* history */

  @volatile private var history =  // owned by Swing thread
    new Change(None, Nil, Future.value(session.begin_document(buffer.getName), Nil))

  def current_change(): Change = history

  def recent_document(): Document =
  {
    def find(change: Change): Document =
      if (change.result.is_finished || !change.parent.isDefined) change.document
      else find(change.parent.get)
    find(current_change())
  }


  /* transforming offsets */

  private def changes_from(doc: Document): List[Edit] =
  {
    Swing_Thread.assert()
    List.flatten(current_change.ancestors(_.document.id == doc.id).reverse.map(_.edits)) :::
      edits_buffer.toList
  }

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


  /* text edits */

  private val edits_buffer = new mutable.ListBuffer[Edit]   // owned by Swing thread

  private val edits_delay = Swing_Thread.delay_last(300) {
    if (!edits_buffer.isEmpty) {
      val edits = edits_buffer.toList
      val change1 = current_change()
      val result: Future[Document.Result] = Future.fork {
        Document.text_edits(session, change1.document, session.create_id(), edits)
      }
      val change2 = new Change(Some(change1), edits, result)
      history = change2
      result.map(_ => session.input(change2))
      edits_buffer.clear
    }
  }


  /* buffer listener */

  private val buffer_listener: BufferListener = new BufferAdapter
  {
    override def contentInserted(buffer: JEditBuffer,
      start_line: Int, offset: Int, num_lines: Int, length: Int)
    {
      edits_buffer += Insert(offset, buffer.getText(offset, length))
      edits_delay()
    }

    override def preContentRemoved(buffer: JEditBuffer,
      start_line: Int, start: Int, num_lines: Int, removed_length: Int)
    {
      edits_buffer += Remove(start, buffer.getText(start, removed_length))
      edits_delay()
    }
  }


  /* activation */

  def activate()
  {
    buffer.setTokenMarker(new Isabelle_Token_Marker(this))
    buffer.addBufferListener(buffer_listener)
    buffer.propertiesChanged()

    edits_buffer += Insert(0, buffer.getText(0, buffer.getLength))
    edits_delay()
  }

  def deactivate()
  {
    buffer.setTokenMarker(buffer.getMode.getTokenMarker)
    buffer.removeBufferListener(buffer_listener)
  }
}
