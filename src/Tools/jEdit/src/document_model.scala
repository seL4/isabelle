/*  Title:      Tools/jEdit/src/document_model.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Document model connected to jEdit buffer (node in theory graph or
auxiliary file).
*/

package isabelle.jedit


import isabelle._

import scala.collection.mutable
import scala.util.parsing.input.CharSequenceReader

import org.gjt.sp.jedit.jEdit
import org.gjt.sp.jedit.Buffer
import org.gjt.sp.jedit.buffer.{BufferAdapter, BufferListener, JEditBuffer, LineManager}


object Document_Model
{
  /* document model of buffer */

  private val key = "PIDE.document_model"

  def apply(buffer: Buffer): Option[Document_Model] =
  {
    GUI_Thread.require {}
    buffer.getProperty(key) match {
      case model: Document_Model => Some(model)
      case _ => None
    }
  }

  def exit(buffer: Buffer)
  {
    GUI_Thread.require {}
    apply(buffer) match {
      case None =>
      case Some(model) =>
        model.deactivate()
        buffer.unsetProperty(key)
        buffer.propertiesChanged
    }
  }

  def init(session: Session, buffer: Buffer, node_name: Document.Node.Name,
    old_model: Option[Document_Model]): Document_Model =
  {
    GUI_Thread.require {}

    old_model match {
      case Some(old)
      if old.node_name == node_name && Isabelle.buffer_token_marker(buffer).isEmpty => old

      case _ =>
        apply(buffer).map(_.deactivate)
        val model = new Document_Model(session, buffer, node_name)
        buffer.setProperty(key, model)
        model.activate()
        buffer.propertiesChanged
        model
    }
  }
}


class Document_Model(val session: Session, val buffer: Buffer, val node_name: Document.Node.Name)
{
  /* header */

  def is_theory: Boolean = node_name.is_theory

  def node_header(): Document.Node.Header =
  {
    GUI_Thread.require {}

    if (is_theory) {
      JEdit_Lib.buffer_lock(buffer) {
        Token_Markup.line_token_iterator(
          Thy_Header.bootstrap_syntax, buffer, 0, buffer.getLineCount).collectFirst(
            {
              case Text.Info(range, tok)
              if tok.is_command && tok.source == Thy_Header.THEORY => range.start
            })
          match {
            case Some(offset) =>
              val length = buffer.getLength - offset
              PIDE.resources.check_thy_reader("", node_name,
                new CharSequenceReader(buffer.getSegment(offset, length)), Token.Pos.command)
            case None => Document.Node.no_header
          }
      }
    }
    else Document.Node.no_header
  }


  /* perspective */

  // owned by GUI thread
  private var _node_required = false
  def node_required: Boolean = _node_required
  def node_required_=(b: Boolean)
  {
    GUI_Thread.require {}
    if (_node_required != b && is_theory) {
      _node_required = b
      PIDE.options_changed()
      PIDE.editor.flush()
    }
  }

  def node_perspective(doc_blobs: Document.Blobs): (Boolean, Document.Node.Perspective_Text) =
  {
    GUI_Thread.require {}

    if (Isabelle.continuous_checking && is_theory) {
      val snapshot = this.snapshot()

      val document_view_ranges =
        for {
          doc_view <- PIDE.document_views(buffer)
          range <- doc_view.perspective(snapshot).ranges
        } yield range

      val load_ranges =
        for {
          cmd <- snapshot.node.load_commands
          blob_name <- cmd.blobs_names
          blob_buffer <- JEdit_Lib.jedit_buffer(blob_name)
          if JEdit_Lib.jedit_text_areas(blob_buffer).nonEmpty
          start <- snapshot.node.command_start(cmd)
          range = snapshot.convert(cmd.proper_range + start)
        } yield range

      val reparse = snapshot.node.load_commands.exists(_.blobs_changed(doc_blobs))

      (reparse,
        Document.Node.Perspective(node_required,
          Text.Perspective(document_view_ranges ::: load_ranges),
          PIDE.editor.node_overlays(node_name)))
    }
    else (false, Document.Node.no_perspective_text)
  }


  /* blob */

  private var _blob: Option[(Bytes, Symbol.Text_Chunk)] = None  // owned by GUI thread

  private def reset_blob(): Unit = GUI_Thread.require { _blob = None }

  def get_blob(): Option[Document.Blob] =
    GUI_Thread.require {
      if (is_theory) None
      else {
        val (bytes, chunk) =
          _blob match {
            case Some(x) => x
            case None =>
              val bytes = PIDE.resources.file_content(buffer)
              val chunk = Symbol.Text_Chunk(buffer.getSegment(0, buffer.getLength))
              _blob = Some((bytes, chunk))
              (bytes, chunk)
          }
        val changed = pending_edits.is_pending()
        Some(Document.Blob(bytes, chunk, changed))
      }
    }


  /* bibtex entries */

  private var _bibtex: Option[List[(String, Text.Offset)]] = None  // owned by GUI thread

  private def reset_bibtex(): Unit = GUI_Thread.require { _bibtex = None }

  def bibtex_entries(): List[(String, Text.Offset)] =
    GUI_Thread.require {
      if (Bibtex_JEdit.check(buffer)) {
        _bibtex match {
          case Some(entries) => entries
          case None =>
            val entries = Bibtex_JEdit.parse_buffer_entries(buffer)
            _bibtex = Some(entries)
            entries
        }
      }
      else Nil
    }


  /* edits */

  def node_edits(
      clear: Boolean,
      text_edits: List[Text.Edit],
      perspective: Document.Node.Perspective_Text): List[Document.Edit_Text] =
  {
    val edits: List[Document.Edit_Text] =
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
    edits.filterNot(_._2.is_void)
  }


  /* pending edits */

  private object pending_edits  // owned by GUI thread
  {
    private var pending_clear = false
    private val pending = new mutable.ListBuffer[Text.Edit]
    private var last_perspective = Document.Node.no_perspective_text

    def is_pending(): Boolean = pending_clear || pending.nonEmpty
    def snapshot(): List[Text.Edit] = pending.toList

    def flushed_edits(doc_blobs: Document.Blobs): List[Document.Edit_Text] =
    {
      val clear = pending_clear
      val edits = snapshot()
      val (reparse, perspective) = node_perspective(doc_blobs)
      if (clear || reparse || edits.nonEmpty || last_perspective != perspective) {
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
      reset_bibtex()

      if (clear) {
        pending_clear = true
        pending.clear
      }
      pending += e
      PIDE.editor.invoke()
    }
  }

  def snapshot(): Document.Snapshot =
    GUI_Thread.require { session.snapshot(node_name, pending_edits.snapshot()) }

  def flushed_edits(doc_blobs: Document.Blobs): List[Document.Edit_Text] =
    GUI_Thread.require { pending_edits.flushed_edits(doc_blobs) }


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


  /* syntax */

  def syntax_changed()
  {
    Untyped.get[LineManager](buffer, "lineMgr").setFirstInvalidLineContext(0)
    for (text_area <- JEdit_Lib.jedit_text_areas(buffer))
      Untyped.method(Class.forName("org.gjt.sp.jedit.textarea.TextArea"), "foldStructureChanged").
        invoke(text_area)
  }

  private def init_token_marker()
  {
    Isabelle.buffer_token_marker(buffer) match {
      case Some(marker) if marker != buffer.getTokenMarker =>
        buffer.setTokenMarker(marker)
        syntax_changed()
      case _ =>
    }
  }


  /* activation */

  private def activate()
  {
    pending_edits.edit(true, Text.Edit.insert(0, JEdit_Lib.buffer_text(buffer)))
    buffer.addBufferListener(buffer_listener)
    init_token_marker()
  }

  private def deactivate()
  {
    buffer.removeBufferListener(buffer_listener)
    init_token_marker()
  }
}
