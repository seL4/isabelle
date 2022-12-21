/*  Title:      Tools/jEdit/src/document_dockable.scala
    Author:     Makarius

Dockable window for document build support.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import scala.swing.{ScrollPane, TextArea, Label, TabbedPane, BorderPanel, Component}
import scala.swing.event.SelectionChanged

import org.gjt.sp.jedit.{jEdit, View}


object Document_Dockable {
  /* state */

  object Status extends Enumeration {
    val WAITING = Value("waiting")
    val RUNNING = Value("running")
    val FINISHED = Value("finished")
  }

  object State {
    def init(): State = State()
  }

  sealed case class State(
    progress: Progress = new Progress,
    process: Future[Unit] = Future.value(()),
    status: Status.Value = Status.FINISHED,
    output: List[XML.Tree] = Nil
  ) {
    def run(progress: Progress, process: Future[Unit]): State =
      copy(progress = progress, process = process, status = Status.RUNNING)

    def finish(output: List[XML.Tree]): State =
      copy(process = Future.value(()), status = Status.FINISHED, output = output)

    def ok: Boolean = !output.exists(Protocol.is_error)
  }
}

class Document_Dockable(view: View, position: String) extends Dockable(view, position) {
  dockable =>

  GUI_Thread.require {}


  /* component state -- owned by GUI thread */

  private val current_state = Synchronized(Document_Dockable.State.init())

  private val process_indicator = new Process_Indicator
  private val pretty_text_area = new Pretty_Text_Area(view)
  private val message_pane = new TabbedPane

  private def show_state(): Unit = GUI_Thread.later {
    val st = current_state.value

    pretty_text_area.update(Document.Snapshot.init, Command.Results.empty, st.output)

    st.status match {
      case Document_Dockable.Status.WAITING =>
        process_indicator.update("Waiting for PIDE document content ...", 5)
      case Document_Dockable.Status.RUNNING =>
        process_indicator.update("Running document build process ...", 15)
      case Document_Dockable.Status.FINISHED =>
        process_indicator.update(null, 0)
    }
  }

  private def show_page(page: TabbedPane.Page): Unit = GUI_Thread.later {
    message_pane.selection.page = page
  }


  /* text area with zoom/resize */

  override def detach_operation: Option[() => Unit] = pretty_text_area.detach_operation

  private val zoom = new Font_Info.Zoom { override def changed(): Unit = handle_resize() }
  private def handle_resize(): Unit = GUI_Thread.require { pretty_text_area.zoom(zoom) }

  private val delay_resize: Delay =
    Delay.first(PIDE.session.update_delay, gui = true) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
    override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
  })


  /* progress log */

  private val log_area =
    new TextArea {
      editable = false
      font = GUI.copy_font((new Label).font)
    }
  private val scroll_log_area = new ScrollPane(log_area)

  def log_progress(): Document_Editor.Log_Progress =
    new Document_Editor.Log_Progress(PIDE.session) {
      override def show(text: String): Unit =
        if (text != log_area.text) {
          log_area.text = text
          val vertical = scroll_log_area.peer.getVerticalScrollBar
          vertical.setValue(vertical.getMaximum)
        }
    }


  /* document build process */

  private def init_state(): Unit =
    current_state.change { _ => Document_Dockable.State(progress = log_progress()) }

  private def cancel_process(): Unit =
    current_state.change { st => st.process.cancel(); st }

  private def await_process(): Unit =
    current_state.guarded_access(st => if (st.process.is_finished) None else Some((), st))

  private def finish_process(output: List[XML.Tree]): Unit =
    current_state.change(_.finish(output))

  private def run_process(body: Document_Editor.Log_Progress => Unit): Boolean = {
    val started =
      current_state.change_result { st =>
        if (st.process.is_finished) {
          val progress = log_progress()
          val process =
            Future.thread[Unit](name = "Document_Dockable.process") {
              await_process()
              body(progress)
            }
          (true, st.run(progress, process))
        }
        else (false, st)
      }
    show_state()
    started
  }

  private def load_document(session: String): Boolean = {
    val options = PIDE.options.value
    run_process { _ =>
      try {
        val session_background =
          Document_Build.session_background(
            options, session, dirs = JEdit_Sessions.session_dirs)
        PIDE.editor.document_setup(Some(session_background))

        finish_process(Nil)
        GUI_Thread.later {
          refresh_theories()
          show_state()
          show_page(theories_page)
        }
      }
      catch {
        case exn: Throwable if !Exn.is_interrupt(exn) =>
          finish_process(List(Protocol.error_message(Exn.print(exn))))
          GUI_Thread.later {
            show_state()
            show_page(output_page)
          }
      }
    }
  }

  private def document_build(
    session_background: Sessions.Background,
    progress: Document_Editor.Log_Progress
  ): Unit = {
    val store = JEdit_Sessions.sessions_store(PIDE.options.value)
    val document_selection = PIDE.editor.document_selection()

    val snapshot = PIDE.session.await_stable_snapshot()
    val session_context =
      Export.open_session_context(store, session_background,
        document_snapshot = Some(snapshot))
    try {
      val context =
        Document_Build.context(session_context,
          document_session = Some(session_background.base),
          document_selection = document_selection,
          progress = progress)
      val variant = session_background.info.documents.head

      Isabelle_System.make_directory(Document_Editor.document_output_dir())
      val doc = context.build_document(variant, verbose = true)

      // log
      File.write(Document_Editor.document_output().log, doc.log)
      GUI_Thread.later { progress.finish(doc.log) }

      // pdf
      Bytes.write(Document_Editor.document_output().pdf, doc.pdf)
      Document_Editor.view_document()
    }
    finally { session_context.close() }
  }

  private def build_document(): Unit = {
    PIDE.editor.document_session() match {
      case Some(session_background) if session_background.info.documents.nonEmpty =>
        run_process { progress =>
          show_page(log_page)
          val res = Exn.capture { document_build(session_background, progress) }
          val msg =
            res match {
              case Exn.Res(_) => Protocol.writeln_message("OK")
              case Exn.Exn(exn) => Protocol.error_message(Exn.print(exn))
            }

          finish_process(List(msg))

          show_state()
          show_page(if (Exn.is_interrupt_exn(res)) theories_page else output_page)
        }
      case _ =>
    }
  }


  /* controls */

  private val document_session =
    JEdit_Sessions.document_selector(PIDE.options, standalone = true)

  private lazy val delay_load: Delay =
    Delay.last(PIDE.session.load_delay, gui = true) {
      for (session <- document_session.selection_value) {
        if (!load_document(session)) delay_load.invoke()
      }
    }

  document_session.reactions += { case SelectionChanged(_) => delay_load.invoke() }

  private val load_button =
    new GUI.Button("Load") {
      tooltip = "Load document theories"
      override def clicked(): Unit = PIDE.editor.document_select_all(set = true)
    }

  private val build_button =
    new GUI.Button("<html><b>Build</b></html>") {
      tooltip = "Build document"
      override def clicked(): Unit = build_document()
    }

  private val cancel_button =
    new GUI.Button("Cancel") {
      tooltip = "Cancel build process"
      override def clicked(): Unit = cancel_process()
    }

  private val view_button =
    new GUI.Button("View") {
      tooltip = "View document"
      override def clicked(): Unit = Document_Editor.view_document()
    }

  private val controls =
    Wrap_Panel(List(document_session, process_indicator.component, load_button,
      build_button, view_button, cancel_button))

  add(controls.peer, BorderLayout.NORTH)

  override def focusOnDefaultComponent(): Unit = build_button.requestFocus()


  /* message pane with pages */

  private val reset_button =
    new GUI.Button("Reset") {
      tooltip = "Deselect document theories"
      override def clicked(): Unit = PIDE.editor.document_select_all(set = false)
    }

  private val purge_button = new GUI.Button("Purge") {
    tooltip = "Remove theories that are no longer required"
    override def clicked(): Unit = PIDE.editor.purge()
  }

  private val theories_controls =
    Wrap_Panel(List(reset_button, purge_button))

  private val theories = new Theories_Status(view, document = true)

  private def refresh_theories(): Unit = {
    val domain = PIDE.editor.document_theories().toSet
    theories.update(domain = Some(domain), trim = true, force = true)
    theories.refresh()
  }

  private val theories_page =
    new TabbedPane.Page("Theories", new BorderPanel {
      layout(theories_controls) = BorderPanel.Position.North
      layout(theories.gui) = BorderPanel.Position.Center
    }, "Selection and status of document theories")

  private val output_controls =
    Wrap_Panel(List(pretty_text_area.search_label, pretty_text_area.search_field, zoom))

  private val output_page =
    new TabbedPane.Page("Output", new BorderPanel {
      layout(output_controls) = BorderPanel.Position.North
      layout(Component.wrap(pretty_text_area)) = BorderPanel.Position.Center
    }, "Output from build process")

  private val log_page =
    new TabbedPane.Page("Log", new BorderPanel {
      layout(scroll_log_area) = BorderPanel.Position.Center
    }, "Raw log of build process")

  message_pane.pages ++= List(theories_page, log_page, output_page)

  set_content(message_pane)


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        GUI_Thread.later {
          document_session.load()
          handle_resize()
          refresh_theories()
        }
      case changed: Session.Commands_Changed =>
        GUI_Thread.later {
          val domain = PIDE.editor.document_theories().filter(changed.nodes).toSet
          if (domain.nonEmpty) theories.update(domain = Some(domain))
        }
    }

  override def init(): Unit = {
    PIDE.editor.document_init(dockable)
    init_state()
    PIDE.session.global_options += main
    PIDE.session.commands_changed += main
    handle_resize()
    delay_load.invoke()
  }

  override def exit(): Unit = {
    PIDE.session.global_options -= main
    PIDE.session.commands_changed -= main
    delay_resize.revoke()
    PIDE.editor.document_exit(dockable)
  }
}
