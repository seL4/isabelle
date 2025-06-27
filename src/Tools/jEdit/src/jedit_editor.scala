/*  Title:      Tools/jEdit/src/jedit_editor.scala
    Author:     Makarius

PIDE editor operations for jEdit.
*/

package isabelle.jedit


import isabelle._


import org.gjt.sp.jedit.{jEdit, View, Buffer}
import org.gjt.sp.jedit.browser.VFSBrowser
import org.gjt.sp.jedit.textarea.TextArea
import org.gjt.sp.jedit.io.{VFSManager, VFSFile}
import org.gjt.sp.util.AwtRunnableQueue


class JEdit_Editor extends Editor[View] {
  /* PIDE session and document model */

  override def session: Session = PIDE.session

  def flush_edits(hidden: Boolean = false, purge: Boolean = false): Unit =
    GUI_Thread.require {
      val (doc_blobs, edits) = Document_Model.flush_edits(hidden, purge)
      session.update(doc_blobs, edits)
    }
  override def flush(): Unit = flush_edits()
  def purge(): Unit = flush_edits(purge = true)

  private val delay_input: Delay =
    Delay.last(PIDE.session.input_delay, gui = true) { flush() }

  private val delay_generated_input: Delay =
    Delay.first(PIDE.session.generated_input_delay, gui = true) { flush() }

  def invoke(): Unit = delay_input.invoke()
  def invoke_generated(): Unit = { delay_input.invoke(); delay_generated_input.invoke() }

  def shutdown(): Unit =
    GUI_Thread.require {
      delay_input.revoke()
      delay_generated_input.revoke()
      Document_Model.flush_edits(hidden = false, purge = false)
    }

  def visible_node(name: Document.Node.Name): Boolean =
    (for {
      text_area <- JEdit_Lib.jedit_text_areas()
      doc_view <- Document_View.get(text_area)
    } yield doc_view.model.node_name).contains(name)


  override def get_models(): Iterable[Document.Model] = Document_Model.get_models()


  /* global changes */

  def state_changed(): Unit = {
    GUI_Thread.later { flush() }
    PIDE.session.deps_changed()
    session.global_options.post(Session.Global_Options(PIDE.options.value))
  }

  override def document_state_changed(): Unit = state_changed()


  /* current situation */

  override def current_node(view: View): Option[Document.Node.Name] =
    GUI_Thread.require { Document_Model.get_model(view.getBuffer).map(_.node_name) }

  override def current_node_snapshot(view: View): Option[Document.Snapshot] =
    GUI_Thread.require { Document_Model.get_snapshot(view.getBuffer) }

  override def node_snapshot(name: Document.Node.Name): Document.Snapshot =
    GUI_Thread.require { Document_Model.get_snapshot(name) getOrElse session.snapshot(name) }

  override def current_command(view: View, snapshot: Document.Snapshot): Option[Command] = {
    GUI_Thread.require {}

    val text_area = view.getTextArea
    val buffer = view.getBuffer

    Document_View.get(text_area) match {
      case Some(doc_view) if doc_view.model.is_theory =>
        snapshot.current_command(doc_view.model.node_name, text_area.getCaretPosition)
      case _ =>
        Document_Model.get_model(buffer) match {
          case Some(model) if !model.is_theory =>
            snapshot.version.nodes.commands_loading(model.node_name).headOption
          case _ => None
        }
    }
  }


  /* overlays */

  override def node_overlays(name: Document.Node.Name): Document.Node.Overlays =
    Document_Model.node_overlays(name)

  override def insert_overlay(command: Command, fn: String, args: List[String]): Unit =
    Document_Model.insert_overlay(command, fn, args)

  override def remove_overlay(command: Command, fn: String, args: List[String]): Unit =
    Document_Model.remove_overlay(command, fn, args)


  /* navigation */

  def goto_file(
    focus: Boolean,
    view: View,
    name: String,
    line: Int = -1,
    offset: Text.Offset = -1,
    at_target: (Buffer, Text.Offset) => Unit = (_, _) => ()
  ): Unit = {
    GUI_Thread.require {}

    PIDE.plugin.navigator.record(view)

    def buffer_offset(buffer: Buffer): Text.Offset =
      ((if (line < 0) 0 else buffer.getLineStartOffset(line min buffer.getLineCount)) +
        (if (offset < 0) 0 else offset)) min buffer.getLength

    JEdit_Lib.jedit_buffer(name) match {
      case Some(buffer) =>
        if (focus) view.goToBuffer(buffer) else view.showBuffer(buffer)
        val target = buffer_offset(buffer)
        view.getTextArea.setCaretPosition(target)
        at_target(buffer, target)

      case None =>
        val is_dir =
          try {
            val vfs = VFSManager.getVFSForPath(name)
            val vfs_file = vfs._getFile((), name, view)
            vfs_file != null && vfs_file.getType == VFSFile.DIRECTORY
          }
          catch { case ERROR(_) => false }

        if (is_dir) VFSBrowser.browseDirectory(view, name)
        else if (!Isabelle_System.open_external_file(name)) {
          val buffer = jEdit.openFile(view, name)
          if (buffer != null && (line >= 0 || offset >= 0)) {
            AwtRunnableQueue.INSTANCE.runAfterIoTasks({ () =>
              val target = buffer_offset(buffer)
              if (view.getBuffer == buffer) {
                view.getTextArea.setCaretPosition(target)
                buffer.setIntegerProperty(Buffer.CARET, target)
                buffer.setBooleanProperty(Buffer.CARET_POSITIONED, true)
                at_target(buffer, target)
              }
              else {
                buffer.setIntegerProperty(Buffer.CARET, target)
                buffer.setBooleanProperty(Buffer.CARET_POSITIONED, true)
                buffer.unsetProperty(Buffer.SCROLL_VERT)
              }
            })
          }
        }
    }
  }

  def goto_doc(view: View, path: Path): Unit = {
    if (path.is_pdf) Doc.view(path)
    else goto_file(true, view, File.platform_path(path))
  }


  /* hyperlinks */

  def hyperlink_doc(name: String): Option[Hyperlink] =
    Doc.contents(PIDE.ml_settings).entries(name = _ == name).headOption.map(entry =>
      new Hyperlink {
        override val external: Boolean = !entry.path.is_file
        def follow(view: View): Unit = goto_doc(view, entry.path)
        override def toString: String = "doc " + quote(name)
      })

  def hyperlink_url(name: String): Hyperlink =
    new Hyperlink {
      override val external = true
      def follow(view: View): Unit =
        Isabelle_Thread.fork(name = "hyperlink_url") {
          try { Isabelle_System.open(Url.escape_name(name)) }
          catch {
            case exn: Throwable =>
              GUI_Thread.later {
                GUI.error_dialog(view, "System error", GUI.scrollable_text(Exn.message(exn)))
              }
          }
        }
      override def toString: String = "URL " + quote(name)
    }

  def hyperlink_file(
    focus: Boolean,
    name: String,
    line: Int = -1,
    offset: Text.Offset = -1
  ): Hyperlink =
    new Hyperlink {
      def follow(view: View): Unit = {
        import Isabelle_Navigator.Pos
        PIDE.plugin.navigator.record(Pos(view))
        goto_file(focus, view, name, line = line, offset = offset,
          at_target = (buffer, target) => Pos.make(JEdit_Lib.buffer_name(buffer), target))
      }
      override def toString: String = "file " + quote(name)
    }

  def hyperlink_source_file(
    focus: Boolean,
    source_name: String,
    line1: Int,
    offset: Symbol.Offset
  ) : Option[Hyperlink] = {
    for (platform_path <- PIDE.session.store.source_file(source_name)) yield {
      def hyperlink(pos: Line.Position) =
        hyperlink_file(focus, platform_path, line = pos.line, offset = pos.column)

      if (offset > 0) {
        PIDE.resources.get_file_content(PIDE.resources.node_name(platform_path)) match {
          case Some(text) =>
            hyperlink(
              Symbol.iterator(text).zipWithIndex.takeWhile(p => p._2 < offset - 1).map(_._1).
                foldLeft(Line.Position.zero)(_.advance(_)))
          case None =>
            hyperlink(Line.Position((line1 - 1) max 0))
        }
      }
      else hyperlink(Line.Position((line1 - 1) max 0))
    }
  }

  override def hyperlink_command(
    focus: Boolean,
    snapshot: Document.Snapshot,
    id: Document_ID.Generic,
    offset: Symbol.Offset = 0
  ) : Option[Hyperlink] = {
    if (snapshot.is_outdated) None
    else {
      snapshot.find_command_position(id, offset)
        .map(pos => hyperlink_file(focus, pos.name, line = pos.line, offset = pos.column))
    }
  }

  def is_hyperlink_position(
    snapshot: Document.Snapshot,
    text_offset: Text.Offset,
    pos: Position.T
  ): Boolean = {
    pos match {
      case Position.Item_Id(id, range) if range.start > 0 =>
        snapshot.find_command(id) match {
          case Some((node, command)) if snapshot.get_node(command.node_name) eq node =>
            node.command_start(command) match {
              case Some(start) => text_offset == start + command.chunk.decode(range.start)
              case None => false
            }
          case _ => false
        }
      case _ => false
    }
  }

  def hyperlink_position(focus: Boolean, snapshot: Document.Snapshot, pos: Position.T)
      : Option[Hyperlink] =
    pos match {
      case Position.Item_File(name, line, range) =>
        hyperlink_source_file(focus, name, line, range.start)
      case Position.Item_Id(id, range) =>
        hyperlink_command(focus, snapshot, id, range.start)
      case _ => None
    }

  def hyperlink_def_position(focus: Boolean, snapshot: Document.Snapshot, pos: Position.T)
      : Option[Hyperlink] =
    pos match {
      case Position.Item_Def_File(name, line, range) =>
        hyperlink_source_file(focus, name, line, range.start)
      case Position.Item_Def_Id(id, range) =>
        hyperlink_command(focus, snapshot, id, range.start)
      case _ => None
    }


  /* dispatcher thread */

  override def assert_dispatcher[A](body: => A): A = GUI_Thread.assert(body)
  override def require_dispatcher[A](body: => A): A = GUI_Thread.require(body)
  override def send_dispatcher(body: => Unit): Unit = GUI_Thread.later(body)
  override def send_wait_dispatcher(body: => Unit): Unit = GUI_Thread.now(body)
}
