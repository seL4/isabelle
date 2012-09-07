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
        buffer.propertiesChanged
    }
  }

  def init(session: Session, buffer: Buffer, name: Document.Node.Name): Document_Model =
  {
    Swing_Thread.require()
    apply(buffer).map(_.deactivate)
    val model = new Document_Model(session, buffer, name)
    buffer.setProperty(key, model)
    model.activate()
    buffer.propertiesChanged
    model
  }
}


class Document_Model(val session: Session, val buffer: Buffer, val name: Document.Node.Name)
{
  /* header */

  def node_header(): Document.Node.Header =
  {
    Swing_Thread.require()
    Isabelle.buffer_lock(buffer) {
      Exn.capture {
        Isabelle.thy_load.check_thy_text(name, buffer.getSegment(0, buffer.getLength))
      } match {
        case Exn.Res(header) => header
        case Exn.Exn(exn) => Document.Node.bad_header(Exn.message(exn))
      }
    }
  }


  /* perspective */

  def buffer_range(): Text.Range = Text.Range(0, (buffer.getLength - 1) max 0)

  def perspective(): Text.Perspective =
  {
    Swing_Thread.require()
    Text.Perspective(
      for {
        doc_view <- Isabelle.document_views(buffer)
        range <- doc_view.perspective().ranges
      } yield range)
  }


  /* pending text edits */

  private object pending_edits  // owned by Swing thread
  {
    private val pending = new mutable.ListBuffer[Text.Edit]
    private var last_perspective: Text.Perspective = Text.Perspective.empty

    def snapshot(): List[Text.Edit] = pending.toList

    def flush()
    {
      Swing_Thread.require()

      val edits = snapshot()
      val new_perspective = perspective()
      if (!edits.isEmpty || last_perspective != new_perspective) {
        pending.clear
        last_perspective = new_perspective
        session.edit_node(name, node_header(), new_perspective, edits)
      }
    }

    private val delay_flush =
      Swing_Thread.delay_last(session.input_delay) { flush() }

    def +=(edit: Text.Edit)
    {
      Swing_Thread.require()
      pending += edit
      delay_flush.invoke()
    }

    def update_perspective()
    {
      delay_flush.invoke()
    }

    def init()
    {
      flush()
      session.init_node(name, node_header(), perspective(), Isabelle.buffer_text(buffer))
    }

    def exit()
    {
      delay_flush.revoke()
      flush()
    }
  }

  def update_perspective()
  {
    Swing_Thread.require()
    pending_edits.update_perspective()
  }

  def full_perspective()
  {
    pending_edits.flush()
    session.edit_node(name, node_header(), Text.Perspective(List(buffer_range())), Nil)
  }


  /* snapshot */

  def snapshot(): Document.Snapshot =
  {
    Swing_Thread.require()
    session.snapshot(name, pending_edits.snapshot())
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
    pending_edits.exit()
    buffer.removeBufferListener(buffer_listener)
    Token_Markup.refresh_buffer(buffer)
  }
}
