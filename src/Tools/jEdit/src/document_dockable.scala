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
    output_results: Command.Results = Command.Results.empty,
    output_main: XML.Body = Nil,
    output_more: XML.Body = Nil
  ) {
    def run(progress: Progress, process: Future[Unit]): State =
      copy(progress = progress, process = process, status = Status.RUNNING)

    def running(results: Command.Results, body: XML.Body): State =
      copy(status = Status.RUNNING, output_results = results, output_main = body)

    def finish(output: XML.Body): State =
      copy(process = Future.value(()), status = Status.FINISHED, output_more = output)

    def output_body: XML.Body =
      output_main :::
      (if (output_main.nonEmpty && output_more.nonEmpty) Pretty.Separator else Nil) :::
      output_more

    def ok: Boolean = !output_body.exists(Protocol.is_error)
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

    pretty_text_area.update(Document.Snapshot.init, st.output_results, st.output_body)

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


  /* progress */

  class Log_Progress extends Program_Progress {
    progress =>

    override def detect_program(s: String): Option[String] =
      Document_Build.detect_running_script(s)

    private val delay: Delay =
      Delay.first(PIDE.session.output_delay) {
        if (!stopped) {
          running_process(progress)
          GUI_Thread.later { show_state() }
        }
      }

    override def echo(msg: String): Unit = { super.echo(msg); delay.invoke() }
    override def stop_program(): Unit = { super.stop_program(); delay.invoke() }
  }


  /* document build process */

  private def init_state(): Unit =
    current_state.change { st =>
      st.progress.stop()
      Document_Dockable.State(progress = new Log_Progress)
    }

  private def cancel_process(): Unit =
    current_state.change { st => st.process.cancel(); st }

  private def await_process(): Unit =
    current_state.guarded_access(st => if (st.process.is_finished) None else Some((), st))

  private def running_process(progress: Log_Progress): Unit = {
    val (results, body) = progress.output()
    current_state.change(_.running(results, body))
  }

  private def finish_process(output: XML.Body): Unit =
    current_state.change(_.finish(output))

  private def run_process(body: Log_Progress => Unit): Boolean = {
    val started =
      current_state.change_result { st =>
        if (st.process.is_finished) {
          st.progress.stop()
          val progress = new Log_Progress
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
          show_page(input_page)
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
    document_session: Document_Editor.Session,
    progress: Log_Progress
  ): Unit = {
    val session_background = document_session.get_background
    val snapshot = document_session.get_snapshot
    val session_context = JEdit_Sessions.open_session_context(document_snapshot = Some(snapshot))
    try {
      val context =
        Document_Build.context(session_context,
          document_session = Some(session_background.base),
          document_selection = document_session.selection,
          progress = progress)

      Isabelle_System.make_directory(Document_Editor.document_output_dir())
      val doc = context.build_document(document_session.get_variant, verbose = true)

      File.write(Document_Editor.document_output().log, doc.log)
      Bytes.write(Document_Editor.document_output().pdf, doc.pdf)
      Document_Editor.view_document()
    }
    finally { session_context.close() }
  }

  private def document_build_attempt(): Boolean = {
    val document_session = PIDE.editor.document_session()
    if (document_session.is_vacuous) true
    else if (document_session.is_pending) false
    else {
      run_process { progress =>
        show_page(output_page)
        val result = Exn.capture { document_build(document_session, progress) }
        val msgs =
          result match {
            case Exn.Res(_) =>
              List(Protocol.writeln_message("OK"))
            case Exn.Exn(exn: Document_Build.Build_Error) =>
              exn.log_errors.map(s => Protocol.error_message(YXML.parse_body(s)))
            case Exn.Exn(exn) =>
              List(Protocol.error_message(YXML.parse_body(Exn.print(exn))))
          }

        progress.stop_program()
        running_process(progress)
        finish_process(Pretty.separate(msgs))

        show_state()
        show_page(if (Exn.is_interrupt_exn(result)) input_page else output_page)
      }
      true
    }
  }

  private lazy val delay_build: Delay =
    Delay.first(PIDE.session.output_delay, gui = true) {
      if (!document_build_attempt()) delay_build.invoke()
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
      override def clicked(): Unit = delay_build.invoke()
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
  private val theories_pane = new ScrollPane(theories.gui)

  private def refresh_theories(): Unit = {
    val domain = PIDE.editor.document_theories().toSet
    theories.update(domain = Some(domain), trim = true, force = true)
    theories.refresh()
  }

  private val input_page =
    new TabbedPane.Page("Input", new BorderPanel {
      layout(theories_controls) = BorderPanel.Position.North
      layout(theories_pane) = BorderPanel.Position.Center
    }, "Selection and status of document theories")

  private val output_controls =
    Wrap_Panel(List(pretty_text_area.search_label, pretty_text_area.search_field, zoom))

  private val output_page =
    new TabbedPane.Page("Output", new BorderPanel {
      layout(output_controls) = BorderPanel.Position.North
      layout(Component.wrap(pretty_text_area)) = BorderPanel.Position.Center
    }, "Results from document build process")

  message_pane.pages ++= List(input_page, output_page)

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
