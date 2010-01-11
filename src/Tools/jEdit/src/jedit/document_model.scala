/*
 * Document model connected to jEdit buffer
 *
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.jedit


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

  private val document_0 = session.begin_document(buffer.getName)

  @volatile private var history =  // owned by Swing thread
    new Change(document_0.id, None, Nil, Future.value(Nil, document_0))

  def current_change(): Change = history
  def recent_document(): Document = current_change().ancestors.find(_.is_assigned).get.join_document


  /* transforming offsets */

  private def changes_from(doc: Document): List[Text_Edit] =
  {
    Swing_Thread.assert()
    (edits_buffer.toList /:
      current_change.ancestors.takeWhile(_.id != doc.id))((edits, change) => change.edits ::: edits)
  }

  def from_current(doc: Document, offset: Int): Int =
    (offset /: changes_from(doc).reverse) ((i, change) => change before i)

  def to_current(doc: Document, offset: Int): Int =
    (offset /: changes_from(doc)) ((i, change) => change after i)

  def lines_of_command(doc: Document, cmd: Command): (Int, Int) =
  {
    val start = doc.command_start(cmd).get  // FIXME total?
    val stop = start + cmd.length
    (buffer.getLineOfOffset(to_current(doc, start)),
     buffer.getLineOfOffset(to_current(doc, stop)))
  }


  /* text edits */

  private val edits_buffer = new mutable.ListBuffer[Text_Edit]   // owned by Swing thread

  private val edits_delay = Swing_Thread.delay_last(300) {
    if (!edits_buffer.isEmpty) {
      val new_change = current_change().edit(session, edits_buffer.toList)
      edits_buffer.clear
      history = new_change
      new_change.result.map(_ => session.input(new_change))
    }
  }


  /* buffer listener */

  private val buffer_listener: BufferListener = new BufferAdapter
  {
    override def contentInserted(buffer: JEditBuffer,
      start_line: Int, offset: Int, num_lines: Int, length: Int)
    {
      edits_buffer += new Text_Edit(true, offset, buffer.getText(offset, length))
      edits_delay()
    }

    override def preContentRemoved(buffer: JEditBuffer,
      start_line: Int, start: Int, num_lines: Int, removed_length: Int)
    {
      edits_buffer += new Text_Edit(false, start, buffer.getText(start, removed_length))
      edits_delay()
    }
  }


  /* activation */

  def activate()
  {
    buffer.setTokenMarker(new Isabelle_Token_Marker(this))
    buffer.addBufferListener(buffer_listener)
    buffer.propertiesChanged()

    edits_buffer += new Text_Edit(true, 0, buffer.getText(0, buffer.getLength))
    edits_delay()
  }

  def deactivate()
  {
    buffer.setTokenMarker(buffer.getMode.getTokenMarker)
    buffer.removeBufferListener(buffer_listener)
  }
}
