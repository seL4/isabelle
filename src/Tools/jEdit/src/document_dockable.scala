/*  Title:      Tools/jEdit/src/document_dockable.scala
    Author:     Makarius

Dockable window for document build support.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import scala.swing.{ScrollPane, TextArea, Label, TabbedPane, BorderPanel, Component}

import org.gjt.sp.jedit.{jEdit, View}


object Document_Dockable {
  /* document output */

  def document_name: String = "document"
  def document_output_dir(): Path = Path.explode("$ISABELLE_HOME_USER/document_output")
  def document_output(): Path = document_output_dir() + Path.basic(document_name)

  def view_document(): Unit = {
    val path = Document_Dockable.document_output().pdf
    if (path.is_file) Isabelle_System.pdf_viewer(path)
  }

  class Log_Progress extends Progress {
    def show(text: String): Unit = {}

    private val syslog = PIDE.session.make_syslog()

    private def update(text: String = syslog.content()): Unit = show(text)
    private val delay =
      Delay.first(PIDE.options.seconds("editor_update_delay"), gui = true) { update() }

    override def echo(msg: String): Unit = { syslog += msg; delay.invoke() }

    def load(): Unit = GUI_Thread.require {
      val path = document_output().log
      val text = if (path.is_file) File.read(path) else ""
      GUI_Thread.later { delay.revoke(); update(text) }
    }

    GUI_Thread.later { update() }
  }


  /* state */

  object Status extends Enumeration {
    val WAITING = Value("waiting")
    val RUNNING = Value("running")
    val FINISHED = Value("finished")
  }

  sealed case class Result(output: List[XML.Tree] = Nil) {
    def failed: Boolean = output.exists(Protocol.is_error)
  }

  object State {
    def empty(): State = State()
    def finish(result: Result): State = State(output = result.output)
  }

  sealed case class State(
    progress: Log_Progress = new Log_Progress,
    process: Future[Unit] = Future.value(()),
    output: List[XML.Tree] = Nil,
    status: Status.Value = Status.FINISHED)
}

class Document_Dockable(view: View, position: String) extends Dockable(view, position) {
  GUI_Thread.require {}


  /* component state -- owned by GUI thread */

  private val current_state = Synchronized(Document_Dockable.State.empty())

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
    Delay.first(PIDE.options.seconds("editor_update_delay"), gui = true) { handle_resize() }

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

  def init_progress(): Document_Dockable.Log_Progress =
    new Document_Dockable.Log_Progress {
      override def show(text: String): Unit =
        if (text != log_area.text) {
          log_area.text = text
          val vertical = scroll_log_area.peer.getVerticalScrollBar
          vertical.setValue(vertical.getMaximum)
        }
    }


  /* document build process */

  private def cancel(): Unit =
    current_state.change { st => st.process.cancel(); st }

  private def init_state(): Unit =
    current_state.change { _ => Document_Dockable.State(progress = init_progress()) }

  private def build_document(): Unit = {
    current_state.change { st =>
      if (st.process.is_finished) {
        val progress = init_progress()
        val process =
          Future.thread[Unit](name = "document_build") {
            show_page(theories_page)
            Time.seconds(2.0).sleep()

            show_page(log_page)
            val res =
              Exn.capture {
                progress.echo("Start " + Date.now())
                for (i <- 1 to 200) {
                  progress.echo("message " + i)
                  Time.seconds(0.1).sleep()
                }
                progress.echo("Stop " + Date.now())
              }
            val msg =
              res match {
                case Exn.Res(_) => Protocol.make_message(XML.string("OK"))
                case Exn.Exn(exn) => Protocol.error_message(XML.string(Exn.message(exn)))
              }
            val result = Document_Dockable.Result(output = List(msg))
            current_state.change(_ => Document_Dockable.State.finish(result))
            show_state()

            show_page(if (Exn.is_interrupt_exn(res)) theories_page else output_page)
            GUI_Thread.later { progress.load() }
          }
        st.copy(progress = progress, process = process, status = Document_Dockable.Status.RUNNING)
      }
      else st
    }
    show_state()
  }


  /* controls */

  private val document_session: GUI.Selector[String] = {
    val sessions = JEdit_Sessions.sessions_structure()
    val all_sessions = sessions.build_topological_order.sorted
    val doc_sessions = all_sessions.filter(name => sessions(name).doc_group)
    new GUI.Selector[String](
      doc_sessions.map(GUI.Selector.item),
      all_sessions.map(GUI.Selector.item)
    ) {
      val title = "Session"
    }
  }

  private val build_button =
    new GUI.Button("<html><b>Build</b></html>") {
      tooltip = "Build document"
      override def clicked(): Unit = build_document()
    }

  private val cancel_button =
    new GUI.Button("Cancel") {
      tooltip = "Cancel build process"
      override def clicked(): Unit = cancel()
    }

  private val view_button =
    new GUI.Button("View") {
      tooltip = "View document"
      override def clicked(): Unit = Document_Dockable.view_document()
    }

  private val controls =
    Wrap_Panel(List(document_session, process_indicator.component, build_button,
      view_button, cancel_button))

  add(controls.peer, BorderLayout.NORTH)

  override def focusOnDefaultComponent(): Unit = build_button.requestFocus()


  /* message pane with pages */

  private val theories = new Theories_Status(view)

  private val theories_page =
    new TabbedPane.Page("Theories", new BorderPanel {
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
          handle_resize()
          theories.reinit()
        }
      case changed: Session.Commands_Changed =>
        GUI_Thread.later {
          theories.update(domain = Some(changed.nodes), trim = changed.assignment)
        }
    }

  override def init(): Unit = {
    init_state()
    PIDE.session.global_options += main
    PIDE.session.commands_changed += main
    theories.update()
    handle_resize()
  }

  override def exit(): Unit = {
    PIDE.session.global_options -= main
    PIDE.session.commands_changed -= main
    delay_resize.revoke()
  }
}
