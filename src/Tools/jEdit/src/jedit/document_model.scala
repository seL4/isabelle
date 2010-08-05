/*  Title:      Tools/jEdit/src/jedit/document_model.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Document model connected to jEdit buffer.
*/

package isabelle.jedit


import isabelle._

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
  /* visible line end */

  // simplify slightly odd result of TextArea.getLineEndOffset
  // NB: jEdit already normalizes \r\n and \r to \n
  def visible_line_end(start: Int, end: Int): Int =
  {
    val end1 = end - 1
    if (start <= end1 && end1 < buffer.getLength &&
        buffer.getSegment(end1, 1).charAt(0) == '\n') end1
    else end
  }


  /* history */

  // FIXME proper error handling
  val thy_name = Thy_Header.split_thy_path(Isabelle.system.posix_path(buffer.getPath))._2

  @volatile private var history = Change.init // owned by Swing thread

  def current_change(): Change = history
  def recent_document(): Document = current_change().ancestors.find(_.is_assigned).get.join_document


  /* transforming offsets */

  private def changes_from(doc: Document): List[Text_Edit] =
  {
    Swing_Thread.assert()
    (edits_buffer.toList /:
      current_change.ancestors.takeWhile(_.id != doc.id))((edits, change) =>
        (for ((name, eds) <- change.edits if name == thy_name) yield eds).flatten ::: edits)
  }

  def from_current(doc: Document, offset: Int): Int =
    (offset /: changes_from(doc).reverse) ((i, change) => change before i)

  def to_current(doc: Document, offset: Int): Int =
    (offset /: changes_from(doc)) ((i, change) => change after i)


  /* text edits */

  private val edits_buffer = new mutable.ListBuffer[Text_Edit]   // owned by Swing thread

  private val edits_delay = Swing_Thread.delay_last(session.input_delay) {
    if (!edits_buffer.isEmpty) {
      val new_change = current_change().edit(session, List((thy_name, edits_buffer.toList)))
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

  private val token_marker = new Isabelle_Token_Marker(this)

  def activate()
  {
    buffer.setTokenMarker(token_marker)
    buffer.addBufferListener(buffer_listener)
    buffer.propertiesChanged()

    edits_buffer += new Text_Edit(true, 0, buffer.getText(0, buffer.getLength))
    edits_delay()
  }

  def refresh()
  {
    buffer.setTokenMarker(token_marker)
  }

  def deactivate()
  {
    buffer.setTokenMarker(buffer.getMode.getTokenMarker)
    buffer.removeBufferListener(buffer_listener)
  }
}
