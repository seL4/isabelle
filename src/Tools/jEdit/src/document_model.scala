/*  Title:      Tools/jEdit/src/document_model.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Document model connected to jEdit buffer -- single node in theory graph.
*/

package isabelle.jedit


import isabelle._

import scala.collection.mutable

import org.gjt.sp.jedit.Buffer
import org.gjt.sp.jedit.buffer.{BufferAdapter, BufferListener, JEditBuffer}
import org.gjt.sp.jedit.textarea.TextArea

import java.awt.font.TextAttribute


object Document_Model
{
  /* document model of buffer */

  private val key = "isabelle.document_model"

  def apply(buffer: Buffer): Option[Document_Model] =
  {
    Swing_Thread.require()
    buffer.getProperty(key) match {
      case model: Document_Model => Some(model)
      case _ => None
    }
  }

  def exit(buffer: Buffer)
  {
    Swing_Thread.require()
    apply(buffer) match {
      case None =>
      case Some(model) =>
        model.deactivate()
        buffer.unsetProperty(key)
    }
  }

  def init(session: Session, buffer: Buffer,
    master_dir: String, node_name: String, thy_name: String): Document_Model =
  {
    exit(buffer)
    val model = new Document_Model(session, buffer, master_dir, node_name, thy_name)
    buffer.setProperty(key, model)
    model.activate()
    model
  }
}


class Document_Model(val session: Session, val buffer: Buffer,
  val master_dir: String, val node_name: String, val thy_name: String)
{
  /* header */

  def node_header(): Exn.Result[Thy_Header] =
  {
    Swing_Thread.require()
    Exn.capture { Thy_Header.check(thy_name, buffer.getSegment(0, buffer.getLength)) }
  }


  /* perspective */

  def perspective(): Text.Perspective =
  {
    Swing_Thread.require()
    Text.perspective(
      for {
        doc_view <- Isabelle.document_views(buffer)
        range <- doc_view.perspective()
      } yield range)
  }


  /* pending text edits */

  private object pending_edits  // owned by Swing thread
  {
    private val pending = new mutable.ListBuffer[Text.Edit]
    private var pending_perspective = false
    def snapshot(): List[Text.Edit] = pending.toList

    def flush()
    {
      Swing_Thread.require()
      snapshot() match {
        case Nil if !pending_perspective =>
        case edits =>
          pending.clear
          pending_perspective = false
          session.edit_node(node_name, master_dir, node_header(), perspective(), edits)
      }
    }

    def init()
    {
      flush()
      session.init_node(node_name, master_dir,
        node_header(), perspective(), Isabelle.buffer_text(buffer))
    }

    private val delay_flush =
      Swing_Thread.delay_last(session.input_delay) { flush() }

    def +=(edit: Text.Edit)
    {
      Swing_Thread.require()
      pending += edit
      delay_flush()
    }

    def update_perspective()
    {
      pending_perspective = true
      delay_flush()
    }
  }

  def update_perspective()
  {
    Swing_Thread.require()
    pending_edits.update_perspective()
  }


  /* snapshot */

  def snapshot(): Document.Snapshot =
  {
    Swing_Thread.require()
    session.snapshot(node_name, pending_edits.snapshot())
  }


  /* buffer listener */

  private val buffer_listener: BufferListener = new BufferAdapter
  {
    override def bufferLoaded(buffer: JEditBuffer)
    {
      pending_edits.init()
    }

    override def contentInserted(buffer: JEditBuffer,
      start_line: Int, offset: Int, num_lines: Int, length: Int)
    {
      if (!buffer.isLoading)
        pending_edits += Text.Edit.insert(offset, buffer.getText(offset, length))
    }

    override def preContentRemoved(buffer: JEditBuffer,
      start_line: Int, offset: Int, num_lines: Int, removed_length: Int)
    {
      if (!buffer.isLoading)
        pending_edits += Text.Edit.remove(offset, buffer.getText(offset, removed_length))
    }
  }


  /* activation */

  private def activate()
  {
    buffer.addBufferListener(buffer_listener)
    pending_edits.init()
    Token_Markup.refresh_buffer(buffer)
  }

  private def deactivate()
  {
    pending_edits.flush()
    buffer.removeBufferListener(buffer_listener)
    Token_Markup.refresh_buffer(buffer)
  }
}
