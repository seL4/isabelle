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

  object State {
    def init(): State = State()
  }

  sealed case class State(
    pending: Boolean = false,
    process: Future[Unit] = Future.value(()),
    progress: Progress = new Progress,
    output_results: Command.Results = Command.Results.empty,
    output_main: XML.Body = Nil,
    output_more: XML.Body = Nil
  ) {
    def running: Boolean = !process.is_finished

    def run(process: Future[Unit], progress: Progress, reset_pending: Boolean): State =
      copy(process = process, progress = progress, pending = if (reset_pending) false else pending)

    def output(results: Command.Results, body: XML.Body): State =
      copy(output_results = results, output_main = body, output_more = Nil)

    def finish(body: XML.Body): State =
      copy(process = Future.value(()), output_more = body)

    def output_body: XML.Body =
      output_main :::
      (if (output_main.nonEmpty && output_more.nonEmpty) Pretty.Separator else Nil) :::
      output_more

    def reset(): State = {
      process.cancel()
      progress.stop()
      State.init()
    }
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

    if (st.running) process_indicator.update("Running document build process ...", 15)
    else if (st.pending) process_indicator.update("Waiting for pending document content ...", 5)
    else process_indicator.update(null, 0)
  }

  private def show_page(page: TabbedPane.Page): Unit = GUI_Thread.later {
    show_state()
    message_pane.selection.page = page
  }


  /* text area with zoom/resize */

  override def detach_operation: Option[() => Unit] = pretty_text_area.detach_operation

  private def handle_resize(): Unit = pretty_text_area.zoom()

  private val delay_resize: Delay =
    Delay.first(PIDE.session.update_delay, gui = true) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
    override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
  })


  /* progress */

  class Log_Progress extends Program_Progress(default_title = "build") {
    progress =>

    override def detect_program(s: String): Option[String] =
      Document_Build.detect_program_start(s)

    private val delay: Delay =
      Delay.first(PIDE.session.output_delay) {
        if (!stopped) {
          output_process(progress)
          show_state()
        }
      }

    override def output(message: Progress.Message): Unit = { super.output(message); delay.invoke() }
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

  private def output_process(progress: Log_Progress): Unit = {
    val (results, body) = progress.output()
    current_state.change(_.output(results, body))
  }

  private def pending_process(): Unit =
    current_state.change { st =>
      if (st.pending) st
      else {
        delay_auto_build.revoke()
        delay_build.invoke()
        st.copy(pending = true)
      }
    }

  private def finish_process(output: XML.Body): Unit =
    current_state.change { st =>
      if (st.pending) {
        delay_auto_build.revoke()
        delay_build.invoke()
      }
      st.finish(output)
    }

  private def run_process(reset_pending: Boolean = false)(body: Log_Progress => Unit): Boolean = {
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
          (true, st.run(process, progress, reset_pending))
        }
        else (false, st)
      }
    show_state()
    started
  }

  private def load_document(session: String): Boolean = {
    val options = PIDE.options.value
    run_process() { _ =>
      try {
        val session_background =
          Document_Build.session_background(
            options, session, dirs = JEdit_Sessions.session_dirs)
        PIDE.editor.document_setup(Some(session_background))

        finish_process(Nil)
        GUI_Thread.later {
          refresh_theories()
          show_page(input_page)
        }
      }
      catch {
        case exn: Throwable if !Exn.is_interrupt(exn) =>
          finish_process(List(Protocol.error_message(Exn.print(exn))))
          show_page(output_page)
      }
    }
  }

  private def document_build_attempt(): Boolean = {
    val document_session = PIDE.editor.document_session()
    if (document_session.is_vacuous) true
    else if (document_session.is_pending) false
    else {
      run_process(reset_pending = true) { progress =>
        output_process(progress)
        show_page(output_page)

        val result = Exn.capture {
          val snapshot = document_session.get_snapshot
          using(JEdit_Sessions.open_session_context(document_snapshot = Some(snapshot)))(
            Document_Editor.build(_, document_session, progress))
        }
        val msgs =
          result match {
            case Exn.Res(_) =>
              List(Protocol.writeln_message("DONE"))
            case Exn.Exn(exn: Document_Build.Build_Error) =>
              exn.log_errors.map(s => Protocol.error_message(YXML.parse_body(YXML.Source(s))))
            case Exn.Exn(exn) =>
              List(Protocol.error_message(YXML.parse_body(YXML.Source(Exn.print(exn)))))
          }

        progress.stop_program()
        output_process(progress)
        progress.stop()
        finish_process(Pretty.separate(msgs))

        show_page(output_page)
      }
      true
    }
  }

  private lazy val delay_build: Delay =
    Delay.first(PIDE.session.output_delay, gui = true) {
      if (!document_build_attempt()) delay_build.invoke()
    }

  private lazy val delay_auto_build: Delay =
    Delay.last(PIDE.session.document_delay, gui = true) {
      pending_process()
    }

  private def document_pending() = current_state.value.pending

  private val document_auto = new JEdit_Options.Bool_Access("editor_document_auto")



  /* controls */

  private val document_session =
    JEdit_Sessions.document_selector(PIDE.options, standalone = true)

  private lazy val delay_load: Delay =
    Delay.last(PIDE.session.load_delay, gui = true) {
      for (session <- document_session.selection_value) {
        current_state.change(_.reset())
        if (!load_document(session)) delay_load.invoke()
        else if (document_auto()) delay_auto_build.invoke()
      }
    }

  document_session.reactions += {
    case SelectionChanged(_) =>
      delay_load.invoke()
      delay_build.revoke()
      delay_auto_build.revoke()
  }

  private val auto_build_button =
    new JEdit_Options.Bool_GUI(document_auto, "Auto") {
      tooltip = Word.capitalized(document_auto.description)
      override def clicked(state: Boolean): Unit = {
        super.clicked(state)

        if (state) delay_auto_build.invoke()
        else delay_auto_build.revoke()
      }
    }

  private val build_button =
    new GUI.Button("<html><b>Build</b></html>") {
      tooltip = "Build document"
      override def clicked(): Unit = pending_process()
    }

  private val view_button =
    new GUI.Button("View") {
      tooltip = "View document"
      override def clicked(): Unit = Document_Editor.view_document()
    }

  private val controls =
    Wrap_Panel(List(document_session, process_indicator.component,
      auto_build_button, build_button, view_button))

  add(controls.peer, BorderLayout.NORTH)

  override def focusOnDefaultComponent(): Unit = build_button.requestFocus()


  /* message pane with pages */

  private val all_button =
    new GUI.Button("All") {
      tooltip = "Select all document theories"
      override def clicked(): Unit = PIDE.editor.document_select_all(set = true)
    }

  private val none_button =
    new GUI.Button("None") {
      tooltip = "Deselect all document theories"
      override def clicked(): Unit = PIDE.editor.document_select_all(set = false)
    }

  private val purge_button = new GUI.Button("Purge") {
    tooltip = "Remove theories that are no longer required"
    override def clicked(): Unit = PIDE.editor.purge()
  }

  private val input_controls =
    Wrap_Panel(List(all_button, none_button, purge_button))

  private val theories = new Theories_Status(view, document = true)
  private val theories_pane = new ScrollPane(theories.gui)

  private def refresh_theories(): Unit = {
    val domain = PIDE.editor.document_theories().toSet
    theories.update(domain = Some(domain), trim = true, force = true)
    theories.refresh()
  }

  private val input_page =
    new TabbedPane.Page("Input", new BorderPanel {
      layout(input_controls) = BorderPanel.Position.North
      layout(theories_pane) = BorderPanel.Position.Center
    }, "Selection and status of document theories")


  private val cancel_button =
    new GUI.Button("Cancel") {
      tooltip = "Cancel build process"
      override def clicked(): Unit = cancel_process()
    }

  private val output_controls = Wrap_Panel(List(cancel_button, pretty_text_area.zoom_component))

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
          if (domain.nonEmpty) {
            theories.update(domain = Some(domain))

            val pending = document_pending()
            val auto = document_auto()
            if ((pending || auto) && PIDE.editor.document_session().is_ready) {
              if (pending) {
                delay_auto_build.revoke()
                delay_build.invoke()
              }
              else if (auto) {
                delay_auto_build.invoke()
              }
            }
          }
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
