/*  Title:      Tools/jEdit/src/plugin.scala
    Author:     Makarius

Main plumbing for PIDE infrastructure as jEdit plugin.
*/

package isabelle.jedit


import isabelle._

import javax.swing.JOptionPane

import scala.swing.{ListView, ScrollPane}

import org.gjt.sp.jedit.{jEdit, EBMessage, EBPlugin, Buffer, View, Debug}
import org.jedit.options.CombinedOptions
import org.gjt.sp.jedit.gui.AboutDialog
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea}
import org.gjt.sp.jedit.syntax.ModeProvider
import org.gjt.sp.jedit.msg.{EditorStarted, BufferUpdate, EditPaneUpdate, PropertiesChanged}

import org.gjt.sp.util.SyntaxUtilities

import scala.actors.Actor._


object PIDE
{
  /* plugin instance */

  val options = new JEdit_Options
  val completion_history = new Completion.History_Variable

  @volatile var startup_failure: Option[Throwable] = None
  @volatile var startup_notified = false

  @volatile var plugin: Plugin = null
  @volatile var session: Session = new Session(new JEdit_Thy_Load(Set.empty, Outer_Syntax.empty))

  def options_changed() {
    session.global_options.event(Session.Global_Options(options.value))
    plugin.load_theories()
  }

  def thy_load(): JEdit_Thy_Load =
    session.thy_load.asInstanceOf[JEdit_Thy_Load]

  lazy val editor = new JEdit_Editor


  /* popups */

  def dismissed_popups(view: View): Boolean =
  {
    var dismissed = false

    JEdit_Lib.jedit_text_areas(view).foreach(text_area =>
      if (Completion_Popup.Text_Area.dismissed(text_area)) dismissed = true)

    if (Pretty_Tooltip.dismissed_all()) dismissed = true

    dismissed
  }


  /* document model and view */

  def document_model(buffer: Buffer): Option[Document_Model] = Document_Model(buffer)

  def document_view(text_area: JEditTextArea): Option[Document_View] = Document_View(text_area)

  def document_views(buffer: Buffer): List[Document_View] =
    for {
      text_area <- JEdit_Lib.jedit_text_areas(buffer).toList
      doc_view <- document_view(text_area)
    } yield doc_view

  def document_models(): List[Document_Model] =
    for {
      buffer <- JEdit_Lib.jedit_buffers().toList
      model <- document_model(buffer)
    } yield model

  def document_blobs(): Document.Blobs =
    document_models().filterNot(_.is_theory).map(model => (model.node_name -> model.blob())).toMap

  def exit_models(buffers: List[Buffer])
  {
    Swing_Thread.now {
      PIDE.editor.flush()
      buffers.foreach(buffer =>
        JEdit_Lib.buffer_lock(buffer) {
          JEdit_Lib.jedit_text_areas(buffer).foreach(Document_View.exit)
          Document_Model.exit(buffer)
        })
      }
  }

  def init_models(buffers: List[Buffer])
  {
    Swing_Thread.now {
      PIDE.editor.flush()
      val init_edits =
        (List.empty[Document.Edit_Text] /: buffers) { case (edits, buffer) =>
          JEdit_Lib.buffer_lock(buffer) {
            if (buffer.getBooleanProperty(Buffer.GZIPPED)) edits
            else {
              val node_name = thy_load.node_name(buffer)
              val (model_edits, model) =
                document_model(buffer) match {
                  case Some(model) if model.node_name == node_name => (Nil, model)
                  case _ =>
                    val model = Document_Model.init(session, buffer, node_name)
                    (model.init_edits(), model)
                }
              for {
                text_area <- JEdit_Lib.jedit_text_areas(buffer)
                if document_view(text_area).map(_.model) != Some(model)
              } Document_View.init(model, text_area)
              model_edits ::: edits
            }
          }
        }
      session.update(document_blobs(), init_edits)
    }
  }

  def init_view(buffer: Buffer, text_area: JEditTextArea)
  {
    JEdit_Lib.swing_buffer_lock(buffer) {
      document_model(buffer) match {
        case Some(model) => Document_View.init(model, text_area)
        case None =>
      }
    }
  }

  def exit_view(buffer: Buffer, text_area: JEditTextArea)
  {
    JEdit_Lib.swing_buffer_lock(buffer) {
      Document_View.exit(text_area)
    }
  }
}


class Plugin extends EBPlugin
{
  /* theory files */

  private lazy val delay_init =
    Swing_Thread.delay_last(PIDE.options.seconds("editor_load_delay"))
    {
      PIDE.init_models(JEdit_Lib.jedit_buffers().toList)
    }

  def load_theories() { Swing_Thread.later { delay_load.invoke() }}

  private lazy val delay_load =
    Swing_Thread.delay_last(PIDE.options.seconds("editor_load_delay"))
    {
      if (Isabelle.continuous_checking) {
        val view = jEdit.getActiveView()

        val buffers = JEdit_Lib.jedit_buffers().toList
        if (buffers.forall(_.isLoaded)) {
          def loaded_buffer(name: String): Boolean =
            buffers.exists(buffer => JEdit_Lib.buffer_name(buffer) == name)

          val thys =
            for {
              buffer <- buffers
              model <- PIDE.document_model(buffer)
              if model.is_theory
            } yield model.node_name

          val thy_info = new Thy_Info(PIDE.thy_load)
          // FIXME avoid I/O in Swing thread!?!
          val files = thy_info.dependencies(thys).deps.map(_.name.node).
            filter(file => !loaded_buffer(file) && PIDE.thy_load.check_file(view, file))

          if (!files.isEmpty) {
            if (PIDE.options.bool("jedit_auto_load")) {
              files.foreach(file => jEdit.openFile(null: View, file))
            }
            else {
              val files_list = new ListView(files.sorted)
              for (i <- 0 until files.length)
                files_list.selection.indices += i

              val answer =
                GUI.confirm_dialog(view,
                  "Auto loading of required files",
                  JOptionPane.YES_NO_OPTION,
                  "The following files are required to resolve theory imports.",
                  "Reload selected files now?",
                  new ScrollPane(files_list),
                  new Isabelle.Continuous_Checking)
              if (answer == 0) {
                files.foreach(file =>
                  if (files_list.selection.items.contains(file))
                    jEdit.openFile(null: View, file))
              }
            }
          }
        }
      }
    }


  /* session manager */

  private val session_manager = actor {
    loop {
      react {
        case phase: Session.Phase =>
          phase match {
            case Session.Inactive | Session.Failed =>
              Swing_Thread.later {
                GUI.error_dialog(jEdit.getActiveView, "Prover process terminated",
                    "Isabelle Syslog", GUI.scrollable_text(PIDE.session.current_syslog()))
              }

            case Session.Ready =>
              PIDE.session.update_options(PIDE.options.value)
              PIDE.init_models(JEdit_Lib.jedit_buffers().toList)
              Swing_Thread.later { delay_load.invoke() }

            case Session.Shutdown =>
              PIDE.exit_models(JEdit_Lib.jedit_buffers().toList)
              Swing_Thread.later { delay_load.revoke() }

            case _ =>
          }
        case bad => java.lang.System.err.println("session_manager: ignoring bad message " + bad)
      }
    }
  }


  /* main plugin plumbing */

  override def handleMessage(message: EBMessage)
  {
    Swing_Thread.assert()

    if (PIDE.startup_failure.isDefined && !PIDE.startup_notified) {
      message match {
        case msg: EditorStarted =>
          GUI.error_dialog(null, "Isabelle plugin startup failure",
            GUI.scrollable_text(Exn.message(PIDE.startup_failure.get)),
            "Prover IDE inactive!")
          PIDE.startup_notified = true
        case _ =>
      }
    }

    if (PIDE.startup_failure.isEmpty) {
      message match {
        case msg: EditorStarted =>
          PIDE.session.start(Isabelle_Logic.session_args())

        case msg: BufferUpdate
        if msg.getWhat == BufferUpdate.LOADED || msg.getWhat == BufferUpdate.PROPERTIES_CHANGED =>
          if (PIDE.session.is_ready) {
            val buffer = msg.getBuffer
            if (buffer != null && !buffer.isLoading) delay_init.invoke()
            load_theories()
          }

        case msg: EditPaneUpdate
        if (msg.getWhat == EditPaneUpdate.BUFFER_CHANGING ||
            msg.getWhat == EditPaneUpdate.BUFFER_CHANGED ||
            msg.getWhat == EditPaneUpdate.CREATED ||
            msg.getWhat == EditPaneUpdate.DESTROYED) =>
          val edit_pane = msg.getEditPane
          val buffer = edit_pane.getBuffer
          val text_area = edit_pane.getTextArea

          if (buffer != null && text_area != null) {
            if (msg.getWhat == EditPaneUpdate.BUFFER_CHANGED ||
                msg.getWhat == EditPaneUpdate.CREATED) {
              if (PIDE.session.is_ready)
                PIDE.init_view(buffer, text_area)
            }
            else {
              PIDE.dismissed_popups(text_area.getView)
              PIDE.exit_view(buffer, text_area)
            }

            if (msg.getWhat == EditPaneUpdate.CREATED)
              Completion_Popup.Text_Area.init(text_area)

            if (msg.getWhat == EditPaneUpdate.DESTROYED)
              Completion_Popup.Text_Area.exit(text_area)
          }

        case msg: PropertiesChanged =>
          PIDE.session.update_options(PIDE.options.value)

        case _ =>
      }
    }
  }

  override def start()
  {
    try {
      Debug.DISABLE_SEARCH_DIALOG_POOL = true

      PIDE.plugin = this
      Isabelle_System.init()
      Isabelle_Font.install_fonts()

      PIDE.options.update(Options.init())
      PIDE.completion_history.load()

      SyntaxUtilities.setStyleExtender(new Token_Markup.Style_Extender)
      if (ModeProvider.instance.isInstanceOf[ModeProvider])
        ModeProvider.instance = new Token_Markup.Mode_Provider(ModeProvider.instance)

      JEdit_Lib.jedit_text_areas.foreach(Completion_Popup.Text_Area.init _)

      val content = Isabelle_Logic.session_content(false)
      val thy_load = new JEdit_Thy_Load(content.loaded_theories, content.syntax)

      PIDE.session = new Session(thy_load) {
        override def output_delay = PIDE.options.seconds("editor_output_delay")
        override def reparse_limit = PIDE.options.int("editor_reparse_limit")
      }

      PIDE.session.phase_changed += session_manager
      PIDE.startup_failure = None
    }
    catch {
      case exn: Throwable =>
        PIDE.startup_failure = Some(exn)
        PIDE.startup_notified = false
    }
  }

  override def stop()
  {
    JEdit_Lib.jedit_text_areas.foreach(Completion_Popup.Text_Area.exit _)

    if (PIDE.startup_failure.isEmpty) {
      PIDE.options.value.save_prefs()
      PIDE.completion_history.value.save()
    }

    PIDE.session.phase_changed -= session_manager
    PIDE.exit_models(JEdit_Lib.jedit_buffers().toList)
    PIDE.session.stop()
  }
}
