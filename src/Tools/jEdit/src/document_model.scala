/*  Title:      Tools/jEdit/src/document_model.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Document model connected to jEdit buffer or external file: content of theory
node or auxiliary file (blob).
*/

package isabelle.jedit


import isabelle._

import java.io.{File => JFile}

import scala.collection.mutable
import scala.annotation.tailrec

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.Buffer
import org.gjt.sp.jedit.buffer.{BufferListener, JEditBuffer}


object Document_Model {
  /* document models */

  sealed case class State(
    models: Map[Document.Node.Name, Document_Model] = Map.empty,
    buffer_models: Map[JEditBuffer, Buffer_Model] = Map.empty,
    overlays: Document.Overlays = Document.Overlays.empty
  ) {
    def file_models_iterator: Iterator[(Document.Node.Name, File_Model)] =
      for {
        (node_name, model) <- models.iterator
        file_model <- Library.as_subclass(classOf[File_Model])(model)
      } yield (node_name, file_model)

    def document_blobs: Document.Blobs =
      Document.Blobs(
        (for {
          (node_name, model) <- models.iterator
          blob <- model.get_blob
        } yield (node_name, blob)).toMap)

    def open_buffer(
      session: Session,
      node_name: Document.Node.Name,
      buffer: Buffer
    ) : (Buffer_Model, State) = {
      val old_model =
        models.get(node_name) match {
          case Some(file_model: File_Model) => Some(file_model)
          case Some(buffer_model: Buffer_Model) => Some(buffer_model.exit())
          case _ => None
        }
      val buffer_model = Buffer_Model.init(old_model, session, node_name, buffer)
      (buffer_model,
        copy(models = models + (node_name -> buffer_model),
          buffer_models = buffer_models + (buffer -> buffer_model)))
    }

    def close_buffer(buffer: JEditBuffer): State = {
      buffer_models.get(buffer) match {
        case None => this
        case Some(buffer_model) =>
          val file_model = buffer_model.exit()
          copy(models = models + (file_model.node_name -> file_model),
            buffer_models = buffer_models - buffer)
      }
    }

    def provide_file(session: Session, node_name: Document.Node.Name, text: String): State =
      if (models.isDefinedAt(node_name)) this
      else {
        val edit = Text.Edit.insert(0, text)
        val content = File_Content(node_name, text)
        val model = File_Model.init(session, content = content, pending_edits = List(edit))
        copy(models = models + (node_name -> model))
      }
  }

  private val state = Synchronized(State())  // owned by GUI thread

  def reset(): Unit = state.change(_ => State())

  def document_blobs(): Document.Blobs = state.value.document_blobs

  def get_models_map(): Map[Document.Node.Name, Document_Model] = state.value.models
  def get_models(): Iterable[Document_Model] = get_models_map().values
  def get_model(name: Document.Node.Name): Option[Document_Model] = get_models_map().get(name)
  def get_model(buffer: JEditBuffer): Option[Buffer_Model] =
    state.value.buffer_models.get(buffer)

  def snapshot(model: Document_Model): Document.Snapshot =
    PIDE.session.snapshot(
      node_name = model.node_name,
      pending_edits = Document.Pending_Edits.make(get_models()))

  def get_snapshot(name: Document.Node.Name): Option[Document.Snapshot] = get_model(name).map(snapshot)
  def get_snapshot(buffer: JEditBuffer): Option[Document.Snapshot] = get_model(buffer).map(snapshot)


  /* overlays */

  def node_overlays(name: Document.Node.Name): Document.Node.Overlays =
    state.value.overlays(name)

  def insert_overlay(command: Command, fn: String, args: List[String]): Unit =
    state.change(st => st.copy(overlays = st.overlays.insert(command, fn, args)))

  def remove_overlay(command: Command, fn: String, args: List[String]): Unit =
    state.change(st => st.copy(overlays = st.overlays.remove(command, fn, args)))


  /* sync external files */

  def sync_files(changed_files: Set[JFile]): Boolean = {
    state.change_result { st =>
      val changed_models =
        (for {
          (node_name, model) <- st.file_models_iterator
          file <- model.file if changed_files(file)
          text <- PIDE.resources.read_file_content(node_name)
          if model.content.text != text
        } yield {
          val content = Document_Model.File_Content(node_name, text)
          val edits = Text.Edit.replace(0, model.content.text, text)
          (node_name, model.copy(content = content, pending_edits = model.pending_edits ::: edits))
        }).toList
      if (changed_models.isEmpty) (false, st)
      else (true, st.copy(models = changed_models.foldLeft(st.models)(_ + _)))
    }
  }


  /* syntax */

  def syntax_changed(names: List[Document.Node.Name]): Unit = {
    GUI_Thread.require {}

    val models = state.value.models
    for {
      name <- names.iterator
      case buffer_model: Buffer_Model <- models.get(name)
    } buffer_model.syntax_changed()
  }


  /* init and exit */

  def init(session: Session, node_name: Document.Node.Name, buffer: Buffer): Buffer_Model = {
    GUI_Thread.require {}
    state.change_result(st =>
      st.buffer_models.get(buffer) match {
        case Some(buffer_model) if buffer_model.node_name == node_name =>
          buffer_model.init_token_marker()
          (buffer_model, st)
        case _ =>
          val res = st.close_buffer(buffer).open_buffer(session, node_name, buffer)
          buffer.propertiesChanged()
          res
      })
  }

  def exit(buffer: Buffer): Unit = {
    GUI_Thread.require {}
    state.change(st =>
      if (st.buffer_models.isDefinedAt(buffer)) {
        val res = st.close_buffer(buffer)
        buffer.propertiesChanged()
        res
      }
      else st)
  }

  def provide_files(session: Session, files: List[(Document.Node.Name, String)]): Unit = {
    GUI_Thread.require {}
    state.change(st =>
      files.foldLeft(st) {
        case (st1, (node_name, text)) => st1.provide_file(session, node_name, text)
      })
  }


  /* required nodes */

  def nodes_required(): Set[Document.Node.Name] =
    (for {
      (node_name, model) <- state.value.models.iterator
      if model.node_required
    } yield node_name).toSet

  def node_required(
    name: Document.Node.Name,
    toggle: Boolean = false,
    set: Boolean = false
  ) : Unit = {
    GUI_Thread.require {}

    val changed =
      state.change_result(st =>
        st.models.get(name) match {
          case None => (false, st)
          case Some(model) =>
            val a = model.node_required
            val b = if (toggle) !a else set
            model match {
              case m: File_Model if a != b =>
                (true, st.copy(models = st.models + (name -> m.set_node_required(b))))
              case m: Buffer_Model if a != b =>
                m.set_node_required(b); (true, st)
              case _ => (false, st)
            }
        })
    if (changed) PIDE.editor.state_changed()
  }

  def view_node_required(
    view: View,
    toggle: Boolean = false,
    set: Boolean = false
  ): Unit =
    Document_Model.get_model(view.getBuffer).foreach(model =>
      node_required(model.node_name, toggle = toggle, set = set))


  /* flushed edits */

  def flush_edits(hidden: Boolean, purge: Boolean): (Document.Blobs, List[Document.Edit_Text]) = {
    GUI_Thread.require {}

    state.change_result({ st =>
      val doc_blobs = st.document_blobs

      val buffer_edits =
        (for {
          (_, model) <- st.buffer_models.iterator
          edit <- model.flush_edits(doc_blobs, hidden).iterator
        } yield edit).toList

      val file_edits =
        (for {
          (node_name, model) <- st.file_models_iterator
          (edits, model1) <- model.flush_edits(doc_blobs, hidden)
        } yield (edits, node_name -> model1)).toList

      val model_edits = buffer_edits ::: file_edits.flatMap(_._1)

      val purge_edits =
        if (purge) {
          val purged =
            (for ((node_name, model) <- st.file_models_iterator)
             yield (node_name -> model.purge_edits(doc_blobs))).toList

          val imports = {
            val open_nodes =
              (for ((_, model) <- st.buffer_models.iterator) yield model.node_name).toList
            val touched_nodes = model_edits.map(_._1)
            val pending_nodes = for (case (node_name, None) <- purged) yield node_name
            (open_nodes ::: touched_nodes ::: pending_nodes).map((_, Position.none))
          }
          val retain = PIDE.resources.dependencies(imports).theories.toSet

          for (case (node_name, Some(edits)) <- purged if !retain(node_name); edit <- edits)
            yield edit
        }
        else Nil

      val st1 = st.copy(models = st.models ++ file_edits.map(_._2) -- purge_edits.map(_._1))
      PIDE.plugin.file_watcher.purge(
        (for {
          (_, model) <- st1.file_models_iterator
          file <- model.file
        } yield file.getParentFile).toSet)

      ((doc_blobs, model_edits ::: purge_edits), st1)
    })
  }


  /* file content */

  object File_Content {
    val empty: File_Content = apply(Document.Node.Name.empty, "")

    def apply(node_name: Document.Node.Name, text: String): File_Content =
      new File_Content(node_name, text)
  }

  final class File_Content private(val node_name: Document.Node.Name, val text: String) {
    override def toString: String = "Document_Model.File_Content(" + node_name.node + ")"
    lazy val bytes: Bytes = Bytes(Symbol.encode(text))
    lazy val chunk: Symbol.Text_Chunk = Symbol.Text_Chunk(text)
    lazy val data: AnyRef = File_Format.registry.parse_data(node_name, text)
  }


  /* HTTP preview */

  object Preview_Service extends HTTP.Service("preview") {
    service =>

    private val plain_text_prefix = "plain_text="

    def server_url(plain_text: Boolean, node_name: Document.Node.Name): String =
      PIDE.plugin.http_server.url + "/" + service.name + "?" +
        (if (plain_text) plain_text_prefix else "") + Url.encode(node_name.node)

    def apply(request: HTTP.Request): Option[HTTP.Response] = GUI_Thread.now {
      for {
        query <- request.decode_query
        name = Library.perhaps_unprefix(plain_text_prefix, query)
        model <- get_model(PIDE.resources.node_name(name))
      }
      yield {
        val snapshot = model.await_stable_snapshot()
        val context =
          Browser_Info.context(PIDE.resources.sessions_structure,
            elements = Browser_Info.extra_elements)
        val document =
          context.preview_document(snapshot,
            plain_text = query.startsWith(plain_text_prefix),
            fonts_css = HTML.fonts_css_dir(HTTP.url_path(request.server_name)))
        HTTP.Response.html(document.content)
      }
    }
  }
}

sealed abstract class Document_Model extends Document.Model {
  model =>


  /* perspective */

  def document_view_ranges(snapshot: Document.Snapshot): List[Text.Range] = Nil

  def node_perspective(
    doc_blobs: Document.Blobs,
    hidden: Boolean
  ): (Boolean, Document.Node.Perspective_Text.T) = {
    GUI_Thread.require {}

    if (JEdit_Options.continuous_checking() && is_theory) {
      val snapshot = Document_Model.snapshot(model)

      val required = node_required || PIDE.editor.document_node_required(node_name)

      val reparse = snapshot.node.load_commands_changed(doc_blobs)
      val perspective =
        if (hidden) Text.Perspective.empty
        else {
          val view_ranges = document_view_ranges(snapshot)
          val load_ranges = snapshot.commands_loading_ranges(PIDE.editor.visible_node)
          Text.Perspective(view_ranges ::: load_ranges)
        }
      val overlays = PIDE.editor.node_overlays(node_name)

      (reparse, Document.Node.Perspective(required, perspective, overlays))
    }
    else (false, Document.Node.Perspective_Text.empty)
  }


  /* snapshot */

  @tailrec final def await_stable_snapshot(): Document.Snapshot = {
    val snapshot = Document_Model.snapshot(model)
    if (snapshot.is_outdated) {
      PIDE.session.output_delay.sleep()
      await_stable_snapshot()
    }
    else snapshot
  }
}

object File_Model {
  def init(session: Session,
    content: Document_Model.File_Content = Document_Model.File_Content.empty,
    node_required: Boolean = false,
    last_perspective: Document.Node.Perspective_Text.T = Document.Node.Perspective_Text.empty,
    pending_edits: List[Text.Edit] = Nil
  ): File_Model = {
    val node_name = content.node_name

    val file = JEdit_Lib.check_file(node_name.node)
    file.foreach(PIDE.plugin.file_watcher.register_parent(_))

    val node_required1 = node_required || File_Format.registry.is_theory(node_name)
    File_Model(session, file, content, node_required1, last_perspective, pending_edits)
  }
}

case class File_Model(
  session: Session,
  file: Option[JFile],
  content: Document_Model.File_Content,
  node_required: Boolean,
  last_perspective: Document.Node.Perspective_Text.T,
  pending_edits: List[Text.Edit]
) extends Document_Model {
  override def toString: String = "file " + quote(node_name.node)


  /* content */

  def node_name: Document.Node.Name = content.node_name

  def get_text(range: Text.Range): Option[String] =
    range.try_substring(content.text)


  /* required */

  def set_node_required(b: Boolean): File_Model = copy(node_required = b)


  /* header */

  def node_header: Document.Node.Header =
    PIDE.resources.special_header(node_name) getOrElse
      PIDE.resources.check_thy(node_name, Scan.char_reader(content.text), strict = false)


  /* content */

  def node_position(offset: Text.Offset): Line.Node_Position =
    Line.Node_Position(node_name.node,
      Line.Position.zero.advance(content.text.substring(0, offset)))

  def get_blob: Option[Document.Blobs.Item] =
    if (is_theory) None
    else {
      val changed = pending_edits.nonEmpty
      Some(Document.Blobs.Item(content.bytes, content.text, content.chunk, changed = changed))
    }

  def untyped_data: AnyRef = content.data


  /* edits */

  def update_text(text: String): Option[File_Model] =
    Text.Edit.replace(0, content.text, text) match {
      case Nil => None
      case edits =>
        val content1 = Document_Model.File_Content(node_name, text)
        val pending_edits1 = pending_edits ::: edits
        Some(copy(content = content1, pending_edits = pending_edits1))
    }

  def flush_edits(
    doc_blobs: Document.Blobs,
    hidden: Boolean
  ): Option[(List[Document.Edit_Text], File_Model)] = {
    val (reparse, perspective) = node_perspective(doc_blobs, hidden)
    if (reparse || pending_edits.nonEmpty || last_perspective != perspective) {
      val edits = node_edits(node_header, pending_edits, perspective)
      Some((edits, copy(last_perspective = perspective, pending_edits = Nil)))
    }
    else None
  }

  def purge_edits(doc_blobs: Document.Blobs): Option[List[Document.Edit_Text]] =
    if (pending_edits.nonEmpty ||
        !File_Format.registry.is_theory(node_name) &&
          (node_required || !Document.Node.Perspective_Text.is_empty(last_perspective))) None
    else {
      val text_edits = List(Text.Edit.remove(0, content.text))
      Some(node_edits(Document.Node.no_header, text_edits, Document.Node.Perspective_Text.empty))
    }

  def is_stable: Boolean = pending_edits.isEmpty
}

object Buffer_Model {
  def init(
    old_model: Option[File_Model],
    session: Session,
    node_name: Document.Node.Name,
    buffer: Buffer
  ): Buffer_Model = (new Buffer_Model(session, node_name, buffer)).init(old_model)
}

class Buffer_Model private(
  val session: Session,
  val node_name: Document.Node.Name,
  val buffer: Buffer
) extends Document_Model {
  override def toString: String = "buffer " + quote(node_name.node)


  /* text */

  def get_text(range: Text.Range): Option[String] =
    JEdit_Lib.get_text(buffer, range)


  /* header */

  def node_header(): Document.Node.Header = {
    GUI_Thread.require {}

    PIDE.resources.special_header(node_name) getOrElse
      JEdit_Lib.buffer_lock(buffer) {
        PIDE.resources.check_thy(node_name, JEdit_Lib.buffer_reader(buffer), strict = false)
      }
  }


  /* perspective */

  def document_view_iterator: Iterator[Document_View] =
    for {
      text_area <- JEdit_Lib.jedit_text_areas(buffer)
      doc_view <- Document_View.get(text_area)
    } yield doc_view

  override def document_view_ranges(snapshot: Document.Snapshot): List[Text.Range] = {
    GUI_Thread.require {}

    (for {
      doc_view <- document_view_iterator
      range <- doc_view.perspective(snapshot).ranges.iterator
    } yield range).toList
  }


  /* mutable buffer state: owned by GUI thread */

  private object buffer_state {
    // perspective and edits

    private var last_perspective = Document.Node.Perspective_Text.empty
    def get_last_perspective: Document.Node.Perspective_Text.T =
      GUI_Thread.require { last_perspective }
    def set_last_perspective(perspective: Document.Node.Perspective_Text.T): Unit =
      GUI_Thread.require { last_perspective = perspective }

    private var node_required = false
    def get_node_required: Boolean = GUI_Thread.require { node_required }
    def set_node_required(b: Boolean): Unit = GUI_Thread.require { node_required = b }

    private val pending_edits = new mutable.ListBuffer[Text.Edit]
    def is_stable: Boolean = GUI_Thread.require { pending_edits.isEmpty }
    def get_pending_edits: List[Text.Edit] = GUI_Thread.require { pending_edits.toList }

    def flush_edits(doc_blobs: Document.Blobs, hidden: Boolean): List[Document.Edit_Text] =
      GUI_Thread.require {
        val edits = get_pending_edits
        val (reparse, perspective) = node_perspective(doc_blobs, hidden)
        if (reparse || edits.nonEmpty || last_perspective != perspective) {
          pending_edits.clear()
          last_perspective = perspective
          node_edits(node_header(), edits, perspective)
        }
        else Nil
      }

    def edit(edits: List[Text.Edit]): Unit = GUI_Thread.require {
      reset_blob()
      reset_data()

      for (doc_view <- document_view_iterator) {
        doc_view.rich_text_area.active_reset()
      }

      pending_edits ++= edits
      PIDE.editor.invoke()
    }

    val listener: BufferListener = JEdit_Lib.buffer_listener((_, e) => edit(List(e)))


    // blob

    private var blob: Option[(Bytes, String, Symbol.Text_Chunk)] = None

    def reset_blob(): Unit = GUI_Thread.require { blob = None }

    def get_blob: Option[Document.Blobs.Item] = GUI_Thread.require {
      if (is_theory) None
      else {
        val (bytes, text, chunk) =
          blob getOrElse {
            val bytes = PIDE.resources.make_file_content(buffer)
            val text = buffer.getText(0, buffer.getLength)
            val chunk = Symbol.Text_Chunk(text)
            val x = (bytes, text, chunk)
            blob = Some(x)
            x
          }
        Some(Document.Blobs.Item(bytes, text, chunk, changed = !is_stable))
      }
    }


    // parsed data

    private var data: Option[AnyRef] = None

    def reset_data(): Unit = GUI_Thread.require { data = None }

    def untyped_data: AnyRef = GUI_Thread.require {
      data getOrElse {
        val text = JEdit_Lib.buffer_text(buffer)
        val res = File_Format.registry.parse_data(node_name, text)
        data = Some(res)
        res
      }
    }
  }

  def is_stable: Boolean = buffer_state.is_stable
  def pending_edits: List[Text.Edit] = buffer_state.get_pending_edits
  def flush_edits(doc_blobs: Document.Blobs, hidden: Boolean): List[Document.Edit_Text] =
    buffer_state.flush_edits(doc_blobs, hidden)

  def node_required: Boolean = buffer_state.get_node_required
  def set_node_required(b: Boolean): Unit = buffer_state.set_node_required(b)

  def get_blob: Option[Document.Blobs.Item] = buffer_state.get_blob
  def untyped_data: AnyRef = buffer_state.untyped_data


  /* syntax */

  def syntax_changed(): Unit = {
    JEdit_Lib.buffer_line_manager(buffer).setFirstInvalidLineContext(0)
    for (text_area <- JEdit_Lib.jedit_text_areas(buffer)) {
      Untyped.method(Class.forName("org.gjt.sp.jedit.textarea.TextArea"), "foldStructureChanged").
        invoke(text_area)
    }
    buffer.invalidateCachedFoldLevels()
  }

  def init_token_marker(): Unit = {
    Isabelle.buffer_token_marker(buffer) match {
      case Some(marker) if marker != buffer.getTokenMarker =>
        buffer.setTokenMarker(marker)
        syntax_changed()
      case _ =>
    }
  }


  /* init */

  def init(old_model: Option[File_Model]): Buffer_Model = GUI_Thread.require {
    old_model match {
      case None =>
        buffer_state.edit(List(Text.Edit.insert(0, JEdit_Lib.buffer_text(buffer))))
      case Some(file_model) =>
        set_node_required(file_model.node_required)
        buffer_state.set_last_perspective(file_model.last_perspective)
        buffer_state.edit(
          file_model.pending_edits :::
            Text.Edit.replace(0, file_model.content.text, JEdit_Lib.buffer_text(buffer)))
    }

    buffer.addBufferListener(buffer_state.listener)
    init_token_marker()

    this
  }


  /* exit */

  def exit(): File_Model = GUI_Thread.require {
    buffer.removeBufferListener(buffer_state.listener)
    init_token_marker()

    File_Model.init(session,
      content = Document_Model.File_Content(node_name, JEdit_Lib.buffer_text(buffer)),
      node_required = node_required,
      last_perspective = buffer_state.get_last_perspective,
      pending_edits = pending_edits)
  }
}
