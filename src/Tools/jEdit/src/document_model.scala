/*  Title:      Tools/jEdit/src/document_model.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Document model connected to jEdit buffer (node in theory graph or
auxiliary file).
*/

package isabelle.jedit


import isabelle._

import scala.collection.mutable

import org.gjt.sp.jedit.Buffer
import org.gjt.sp.jedit.buffer.{BufferAdapter, BufferListener, JEditBuffer}


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

  def is_theory: Boolean = node_name.is_theory

  def node_header(): Document.Node.Header =
  {
    Swing_Thread.require()

    if (is_theory) {
      JEdit_Lib.buffer_lock(buffer) {
        Exn.capture {
          PIDE.resources.check_thy_text(node_name, buffer.getSegment(0, buffer.getLength))
        } match {
          case Exn.Res(header) => header
          case Exn.Exn(exn) => Document.Node.bad_header(Exn.message(exn))
        }
      }
    }
    else Document.Node.no_header
  }


  /* perspective */

  // owned by Swing thread
  private var _node_required = false
  def node_required: Boolean = _node_required
  def node_required_=(b: Boolean)
  {
    Swing_Thread.require()
    if (_node_required != b && is_theory) {
      _node_required = b
      PIDE.options_changed()
      PIDE.editor.flush()
    }
  }

  val empty_perspective: Document.Node.Perspective_Text =
    Document.Node.Perspective(false, Text.Perspective.empty, Document.Node.Overlays.empty)

  def node_perspective(doc_blobs: Document.Blobs): (Boolean, Document.Node.Perspective_Text) =
  {
    Swing_Thread.require()

    if (Isabelle.continuous_checking && is_theory) {
      val snapshot = this.snapshot()

      val document_view_ranges =
        if (is_theory) {
          for {
            doc_view <- PIDE.document_views(buffer)
            range <- doc_view.perspective(snapshot).ranges
          } yield range
        }
        else Nil

      val load_ranges =
        for {
          cmd <- snapshot.node.load_commands
          blob_name <- cmd.blobs_names
          blob_buffer <- JEdit_Lib.jedit_buffer(blob_name)
          if !JEdit_Lib.jedit_text_areas(blob_buffer).isEmpty
          start <- snapshot.node.command_start(cmd)
          range = snapshot.convert(cmd.proper_range + start)
        } yield range

      val reparse = snapshot.node.load_commands.exists(_.blobs_changed(doc_blobs))

      (reparse,
        Document.Node.Perspective(node_required,
          Text.Perspective(document_view_ranges ::: load_ranges),
          PIDE.editor.node_overlays(node_name)))
    }
    else (false, empty_perspective)
  }


  /* blob */

  private var _blob: Option[(Bytes, Command.Chunk.File)] = None  // owned by Swing thread

  private def reset_blob(): Unit = Swing_Thread.require { _blob = None }

  def get_blob(): Option[Document.Blob] =
    Swing_Thread.require {
      if (is_theory) None
      else {
        val (bytes, file) =
          _blob match {
            case Some(x) => x
            case None =>
              val bytes = PIDE.resources.file_content(buffer)
              val file =
                new Command.Chunk.File(node_name.node, buffer.getSegment(0, buffer.getLength))
              _blob = Some((bytes, file))
              (bytes, file)
          }
        val changed = pending_edits.is_pending()
        Some(Document.Blob(bytes, file, changed))
      }
    }


  /* edits */

  def node_edits(
      clear: Boolean,
      text_edits: List[Text.Edit],
      perspective: Document.Node.Perspective_Text): List[Document.Edit_Text] =
    get_blob() match {
      case None =>
        val header_edit = session.header_edit(node_name, node_header())
        if (clear)
          List(header_edit,
            node_name -> Document.Node.Clear(),
            node_name -> Document.Node.Edits(text_edits),
            node_name -> perspective)
        else
          List(header_edit,
            node_name -> Document.Node.Edits(text_edits),
            node_name -> perspective)
      case Some(blob) =>
        List(node_name -> Document.Node.Blob(blob),
          node_name -> Document.Node.Edits(text_edits))
    }


  /* pending edits */

  private object pending_edits  // owned by Swing thread
  {
    private var pending_clear = false
    private val pending = new mutable.ListBuffer[Text.Edit]
    private var last_perspective = empty_perspective

    def is_pending(): Boolean = pending_clear || !pending.isEmpty
    def snapshot(): List[Text.Edit] = pending.toList

    def flushed_edits(doc_blobs: Document.Blobs): List[Document.Edit_Text] =
    {
      val clear = pending_clear
      val edits = snapshot()
      val (reparse, perspective) = node_perspective(doc_blobs)
      if (clear || reparse || !edits.isEmpty || last_perspective != perspective) {
        pending_clear = false
        pending.clear
        last_perspective = perspective
        node_edits(clear, edits, perspective)
      }
      else Nil
    }

    def edit(clear: Boolean, e: Text.Edit)
    {
      reset_blob()

      if (clear) {
        pending_clear = true
        pending.clear
      }
      pending += e
      PIDE.editor.invoke()
    }
  }

  def snapshot(): Document.Snapshot =
    Swing_Thread.require { session.snapshot(node_name, pending_edits.snapshot()) }

  def flushed_edits(doc_blobs: Document.Blobs): List[Document.Edit_Text] =
    Swing_Thread.require { pending_edits.flushed_edits(doc_blobs) }


  /* buffer listener */

  private val buffer_listener: BufferListener = new BufferAdapter
  {
    override def bufferLoaded(buffer: JEditBuffer)
    {
      pending_edits.edit(true, Text.Edit.insert(0, JEdit_Lib.buffer_text(buffer)))
    }

    override def contentInserted(buffer: JEditBuffer,
      start_line: Int, offset: Int, num_lines: Int, length: Int)
    {
      if (!buffer.isLoading)
        pending_edits.edit(false, Text.Edit.insert(offset, buffer.getText(offset, length)))
    }

    override def preContentRemoved(buffer: JEditBuffer,
      start_line: Int, offset: Int, num_lines: Int, removed_length: Int)
    {
      if (!buffer.isLoading)
        pending_edits.edit(false, Text.Edit.remove(offset, buffer.getText(offset, removed_length)))
    }
  }


  /* activation */

  private def activate()
  {
    pending_edits.edit(true, Text.Edit.insert(0, JEdit_Lib.buffer_text(buffer)))
    buffer.addBufferListener(buffer_listener)
    Token_Markup.refresh_buffer(buffer)
  }

  private def deactivate()
  {
    buffer.removeBufferListener(buffer_listener)
    Token_Markup.refresh_buffer(buffer)
  }
}
