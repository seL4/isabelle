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

  private val key = "PIDE.document_model"

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

  def init(session: Session, buffer: Buffer, node_name: Document.Node.Name): Document_Model =
  {
    Swing_Thread.require()
    apply(buffer).map(_.deactivate)
    val model = new Document_Model(session, buffer, node_name)
    buffer.setProperty(key, model)
    model.activate()
    buffer.propertiesChanged
    model
  }
}


class Document_Model(val session: Session, val buffer: Buffer, val node_name: Document.Node.Name)
{
  /* header */

  def node_header(): Document.Node.Header =
  {
    Swing_Thread.require()
    JEdit_Lib.buffer_lock(buffer) {
      Exn.capture {
        PIDE.thy_load.check_thy_text(node_name, buffer.getSegment(0, buffer.getLength))
      } match {
        case Exn.Res(header) => header
        case Exn.Exn(exn) => Document.Node.bad_header(Exn.message(exn))
      }
    }
  }


  /* overlays */

  private var overlays = Document.Node.Overlays.empty

  def insert_overlay(command: Command, name: String, args: List[String]): Unit =
    Swing_Thread.require { overlays = overlays.insert(command, (name, args)) }

  def remove_overlay(command: Command, name: String, args: List[String]): Unit =
    Swing_Thread.require { overlays = overlays.remove(command, (name, args)) }


  /* perspective */

  // owned by Swing thread
  private var _node_required = false
  def node_required: Boolean = _node_required
  def node_required_=(b: Boolean)
  {
    Swing_Thread.require()
    if (_node_required != b) {
      _node_required = b
      PIDE.options_changed()
      PIDE.flush_buffers()
    }
  }

  val empty_perspective: Document.Node.Perspective_Text =
    Document.Node.Perspective(false, Text.Perspective.empty, Document.Node.Overlays.empty)

  def node_perspective(): Document.Node.Perspective_Text =
  {
    Swing_Thread.require()

    if (Isabelle.continuous_checking) {
      Document.Node.Perspective(node_required, Text.Perspective(
        for {
          doc_view <- PIDE.document_views(buffer)
          range <- doc_view.perspective().ranges
        } yield range), overlays)
    }
    else empty_perspective
  }


  /* edits */

  def init_edits(): List[Document.Edit_Text] =
  {
    Swing_Thread.require()

    val header = node_header()
    val text = JEdit_Lib.buffer_text(buffer)
    val perspective = node_perspective()

    List(session.header_edit(node_name, header),
      node_name -> Document.Node.Clear(),
      node_name -> Document.Node.Edits(List(Text.Edit.insert(0, text))),
      node_name -> perspective)
  }

  def node_edits(perspective: Document.Node.Perspective_Text, text_edits: List[Text.Edit])
    : List[Document.Edit_Text] =
  {
    Swing_Thread.require()

    val header = node_header()

    List(session.header_edit(node_name, header),
      node_name -> Document.Node.Edits(text_edits),
      node_name -> perspective)
  }


  /* pending edits */

  private object pending_edits  // owned by Swing thread
  {
    private val pending = new mutable.ListBuffer[Text.Edit]
    private var last_perspective = empty_perspective

    def snapshot(): List[Text.Edit] = pending.toList

    def flushed_edits(): List[Document.Edit_Text] =
    {
      Swing_Thread.require()

      val edits = snapshot()
      val new_perspective = node_perspective()
      if (!edits.isEmpty || last_perspective != new_perspective) {
        pending.clear
        last_perspective = new_perspective
        node_edits(new_perspective, edits)
      }
      else Nil
    }

    def flush(): Unit = session.update(flushed_edits())

    val delay_flush =
      Swing_Thread.delay_last(PIDE.options.seconds("editor_input_delay")) { flush() }

    def +=(edit: Text.Edit)
    {
      Swing_Thread.require()
      pending += edit
      delay_flush.invoke()
    }

    def init()
    {
      flush()
      session.update(init_edits())
    }

    def exit()
    {
      delay_flush.revoke()
      flush()
    }
  }

  def flushed_edits(): List[Document.Edit_Text] = pending_edits.flushed_edits()

  def update_perspective(): Unit = pending_edits.delay_flush.invoke()


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
    pending_edits.flush()
    Token_Markup.refresh_buffer(buffer)
  }

  private def deactivate()
  {
    pending_edits.exit()
    buffer.removeBufferListener(buffer_listener)
    Token_Markup.refresh_buffer(buffer)
  }
}
