/*  Title:      Tools/jEdit/src/plugin.scala
    Author:     Makarius

Main plumbing for PIDE infrastructure as jEdit plugin.
*/

package isabelle.jedit


import isabelle._

import javax.swing.JOptionPane

import java.io.{File => JFile}

import scala.swing.{ListView, ScrollPane}

import org.gjt.sp.jedit.{jEdit, EBMessage, EBPlugin, Buffer, View, Debug, PerspectiveManager}
import org.gjt.sp.jedit.gui.AboutDialog
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.syntax.ModeProvider
import org.gjt.sp.jedit.msg.{EditorStarted, BufferUpdate, EditPaneUpdate, PropertiesChanged}
import org.gjt.sp.util.SyntaxUtilities
import org.gjt.sp.util.Log


object PIDE
{
  /* plugin instance */

  @volatile var _plugin: Plugin = null

  def plugin: Plugin =
    if (_plugin == null) error("Uninitialized Isabelle/jEdit plugin")
    else _plugin
  def options: JEdit_Options = plugin.options

  @volatile var session: Session = new Session(JEdit_Resources.empty)

  def resources(): JEdit_Resources =
    session.resources.asInstanceOf[JEdit_Resources]

  def debugger: Debugger = session.debugger

  lazy val editor = new JEdit_Editor


  /* current document content */

  def snapshot(view: View): Document.Snapshot = GUI_Thread.now
  {
    Document_Model.get(view.getBuffer) match {
      case Some(model) => model.snapshot
      case None => error("No document model for current buffer")
    }
  }

  def rendering(view: View): JEdit_Rendering = GUI_Thread.now
  {
    val text_area = view.getTextArea
    Document_View.get(text_area) match {
      case Some(doc_view) => doc_view.get_rendering()
      case None => error("No document view for current text area")
    }
  }
}


class Plugin extends EBPlugin
{
  /* early initialization */

  val options: JEdit_Options =
  {
    // adhoc patch of confusing message
    val plugin_error = jEdit.getProperty("plugin-error.start-error")
    jEdit.setProperty("plugin-error.start-error", "Cannot start plugin:\n{0}")

    val options = new JEdit_Options(Options.init())

    jEdit.setProperty("plugin-error.start-error", plugin_error)

    options
  }

  val completion_history = new Completion.History_Variable
  val spell_checker = new Spell_Checker_Variable

  PIDE._plugin = this


  /* global changes */

  def options_changed()
  {
    PIDE.session.global_options.post(Session.Global_Options(PIDE.options.value))
    delay_load.invoke()
  }

  def deps_changed()
  {
    delay_load.invoke()
  }


  /* theory files */

  lazy val delay_init =
    GUI_Thread.delay_last(PIDE.options.seconds("editor_load_delay"))
    {
      init_models()
    }

  private val delay_load_active = Synchronized(false)
  private def delay_load_activated(): Boolean =
    delay_load_active.guarded_access(a => Some((!a, true)))
  private def delay_load_action()
  {
    if (Isabelle.continuous_checking && delay_load_activated() &&
        PerspectiveManager.isPerspectiveEnabled)
    {
      if (JEdit_Lib.jedit_buffers().exists(_.isLoading)) delay_load.invoke()
      else {
        val required_files =
        {
          val models = Document_Model.get_models()

          val thys =
            (for ((node_name, model) <- models.iterator if model.is_theory)
              yield (node_name, Position.none)).toList
          val thy_files = PIDE.resources.thy_info.dependencies("", thys).deps.map(_.name)

          val aux_files =
            if (PIDE.options.bool("jedit_auto_resolve")) {
              val stable_tip_version =
                if (models.forall(p => p._2.is_stable))
                  PIDE.session.current_state().stable_tip_version
                else None
              stable_tip_version match {
                case Some(version) => PIDE.resources.undefined_blobs(version.nodes)
                case None => delay_load.invoke(); Nil
              }
            }
            else Nil

          (thy_files ::: aux_files).filterNot(models.isDefinedAt(_))
        }
        if (required_files.nonEmpty) {
          try {
            Standard_Thread.fork("resolve_dependencies") {
              val loaded_files =
                for {
                  name <- required_files
                  text <- PIDE.resources.read_file_content(name)
                } yield (name, text)

              GUI_Thread.later {
                try {
                  Document_Model.provide_files(PIDE.session, loaded_files)
                  delay_init.invoke()
                }
                finally { delay_load_active.change(_ => false) }
              }
            }
          }
          catch { case _: Throwable => delay_load_active.change(_ => false) }
        }
        else delay_load_active.change(_ => false)
      }
    }
  }

  private lazy val delay_load =
    GUI_Thread.delay_last(PIDE.options.seconds("editor_load_delay")) { delay_load_action() }

  private def file_watcher_action(changed: Set[JFile]): Unit =
    if (Document_Model.sync_files(changed)) PIDE.editor.invoke_generated()

  lazy val file_watcher: File_Watcher =
    File_Watcher(file_watcher_action _, PIDE.options.seconds("editor_load_delay"))


  /* session phase */

  val session_phase_changed: Session.Phase => Unit =
  {
    case Session.Terminated(_) =>
      GUI_Thread.later {
        GUI.error_dialog(jEdit.getActiveView, "Prover process terminated",
          "Isabelle Syslog", GUI.scrollable_text(PIDE.session.syslog_content()))
      }

    case Session.Ready =>
      PIDE.session.update_options(PIDE.options.value)
      init_models()

      if (!Isabelle.continuous_checking) {
        GUI_Thread.later {
          val answer =
            GUI.confirm_dialog(jEdit.getActiveView,
              "Continuous checking of PIDE document",
              JOptionPane.YES_NO_OPTION,
              "Continuous checking is presently disabled:",
              "editor buffers will remain inactive!",
              "Enable continuous checking now?")
          if (answer == 0) Isabelle.continuous_checking = true
        }
      }

      delay_load.invoke()

    case Session.Shutdown =>
      GUI_Thread.later {
        delay_load.revoke()
        delay_init.revoke()
        PIDE.editor.flush()
        exit_models(JEdit_Lib.jedit_buffers().toList)
      }

    case _ =>
  }


  /* document model and view */

  def exit_models(buffers: List[Buffer])
  {
    GUI_Thread.now {
      buffers.foreach(buffer =>
        JEdit_Lib.buffer_lock(buffer) {
          JEdit_Lib.jedit_text_areas(buffer).foreach(Document_View.exit)
          Document_Model.exit(buffer)
        })
      }
  }

  def init_models()
  {
    GUI_Thread.now {
      PIDE.editor.flush()

      for {
        buffer <- JEdit_Lib.jedit_buffers()
        if buffer != null && !buffer.getBooleanProperty(Buffer.GZIPPED)
      } {
        if (buffer.isLoaded) {
          JEdit_Lib.buffer_lock(buffer) {
            val node_name = PIDE.resources.node_name(buffer)
            val model = Document_Model.init(PIDE.session, node_name, buffer)
            for {
              text_area <- JEdit_Lib.jedit_text_areas(buffer)
              if Document_View.get(text_area).map(_.model) != Some(model)
            } Document_View.init(model, text_area)
          }
        }
        else delay_init.invoke()
      }

      PIDE.editor.invoke_generated()
    }
  }

  def init_view(buffer: Buffer, text_area: JEditTextArea): Unit =
    GUI_Thread.now {
      JEdit_Lib.buffer_lock(buffer) {
        Document_Model.get(buffer) match {
          case Some(model) => Document_View.init(model, text_area)
          case None =>
        }
      }
    }

  def exit_view(buffer: Buffer, text_area: JEditTextArea): Unit =
    GUI_Thread.now {
      JEdit_Lib.buffer_lock(buffer) {
        Document_View.exit(text_area)
      }
    }


  /* main plugin plumbing */

  @volatile private var startup_failure: Option[Throwable] = None
  @volatile private var startup_notified = false

  override def handleMessage(message: EBMessage)
  {
    GUI_Thread.assert {}

    if (startup_failure.isDefined && !startup_notified) {
      message match {
        case msg: EditorStarted =>
          GUI.error_dialog(null, "Isabelle plugin startup failure",
            GUI.scrollable_text(Exn.message(startup_failure.get)),
            "Prover IDE inactive!")
          startup_notified = true
        case _ =>
      }
    }

    if (startup_failure.isEmpty) {
      message match {
        case msg: EditorStarted =>
          if (Distribution.is_identified && !Distribution.is_official) {
            GUI.warning_dialog(jEdit.getActiveView, "Isabelle version for testing",
              "This is " + Distribution.version + ".",
              "It is for testing only, not for production use.")
          }

          val view = jEdit.getActiveView()

          Session_Build.session_build(view)

          Keymap_Merge.check_dialog(view)

          PIDE.editor.hyperlink_position(true, Document.Snapshot.init,
            JEdit_Sessions.session_info().open_root).foreach(_.follow(view))

        case msg: BufferUpdate
        if msg.getWhat == BufferUpdate.LOAD_STARTED || msg.getWhat == BufferUpdate.CLOSING =>
          if (msg.getBuffer != null) {
            exit_models(List(msg.getBuffer))
            PIDE.editor.invoke_generated()
          }

        case msg: BufferUpdate
        if msg.getWhat == BufferUpdate.PROPERTIES_CHANGED || msg.getWhat == BufferUpdate.LOADED =>
          if (PIDE.session.is_ready) {
            delay_init.invoke()
            delay_load.invoke()
          }

        case msg: EditPaneUpdate
        if msg.getWhat == EditPaneUpdate.BUFFER_CHANGING ||
            msg.getWhat == EditPaneUpdate.BUFFER_CHANGED ||
            msg.getWhat == EditPaneUpdate.CREATED ||
            msg.getWhat == EditPaneUpdate.DESTROYED =>
          val edit_pane = msg.getEditPane
          val buffer = edit_pane.getBuffer
          val text_area = edit_pane.getTextArea

          if (buffer != null && text_area != null) {
            if (msg.getWhat == EditPaneUpdate.BUFFER_CHANGED ||
                msg.getWhat == EditPaneUpdate.CREATED) {
              if (PIDE.session.is_ready)
                init_view(buffer, text_area)
            }
            else {
              Isabelle.dismissed_popups(text_area.getView)
              exit_view(buffer, text_area)
            }

            if (msg.getWhat == EditPaneUpdate.CREATED)
              Completion_Popup.Text_Area.init(text_area)

            if (msg.getWhat == EditPaneUpdate.DESTROYED)
              Completion_Popup.Text_Area.exit(text_area)
          }

        case msg: PropertiesChanged =>
          for {
            view <- JEdit_Lib.jedit_views
            edit_pane <- JEdit_Lib.jedit_edit_panes(view)
          } {
            val buffer = edit_pane.getBuffer
            val text_area = edit_pane.getTextArea
            if (buffer != null && text_area != null) init_view(buffer, text_area)
          }

          spell_checker.update(PIDE.options.value)
          PIDE.session.update_options(PIDE.options.value)

        case _ =>
      }
    }
  }

  override def start()
  {
    try {
      Debug.DISABLE_SEARCH_DIALOG_POOL = true

      completion_history.load()
      spell_checker.update(PIDE.options.value)

      SyntaxUtilities.setStyleExtender(new Token_Markup.Style_Extender)
      if (ModeProvider.instance.isInstanceOf[ModeProvider])
        ModeProvider.instance = new Token_Markup.Mode_Provider(ModeProvider.instance)

      JEdit_Lib.jedit_text_areas.foreach(Completion_Popup.Text_Area.init _)

      val resources = new JEdit_Resources(JEdit_Sessions.session_base())

      PIDE.session.stop()
      PIDE.session = new Session(resources) {
        override def output_delay = PIDE.options.seconds("editor_output_delay")
        override def prune_delay = PIDE.options.seconds("editor_prune_delay")
        override def syslog_limit = PIDE.options.int("editor_syslog_limit")
        override def reparse_limit = PIDE.options.int("editor_reparse_limit")
      }

      startup_failure = None
    }
    catch {
      case exn: Throwable =>
        startup_failure = Some(exn)
        startup_notified = false
        Log.log(Log.ERROR, this, exn)
    }
  }

  override def stop()
  {
    JEdit_Lib.jedit_text_areas.foreach(Completion_Popup.Text_Area.exit _)

    if (startup_failure.isEmpty) {
      PIDE.options.value.save_prefs()
      completion_history.value.save()
    }

    exit_models(JEdit_Lib.jedit_buffers().toList)
    PIDE.session.stop()
    file_watcher.shutdown()
  }
}
