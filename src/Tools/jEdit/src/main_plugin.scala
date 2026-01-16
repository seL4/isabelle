/*  Title:      Tools/jEdit/src/main_plugin.scala
    Author:     Makarius

Main plumbing for PIDE infrastructure as jEdit plugin.
*/

package isabelle.jedit


import isabelle._

import javax.swing.JOptionPane

import java.io.{File => JFile}

import org.gjt.sp.jedit.{jEdit, EBMessage, EBPlugin, Buffer, View, PerspectiveManager}
import org.gjt.sp.jedit.textarea.JEditTextArea
import org.gjt.sp.jedit.syntax.ModeProvider
import org.gjt.sp.jedit.msg.{EditorStarted, BufferUpdate, BufferChanging, PositionChanging,
  EditPaneUpdate, PropertiesChanged, ViewUpdate}
import org.gjt.sp.util.Log


object PIDE {
  /* semantic document content */

  def maybe_snapshot(view: View = null): Option[Document.Snapshot] = GUI_Thread.now {
    val buffer = JEdit_Lib.jedit_view(view).getBuffer
    Document_Model.get_snapshot(buffer)
  }

  def maybe_rendering(view: View = null): Option[JEdit_Rendering] = GUI_Thread.now {
    val text_area = JEdit_Lib.jedit_view(view).getTextArea
    Document_View.get_rendering(text_area)
  }

  def snapshot(view: View = null): Document.Snapshot =
    maybe_snapshot(view) getOrElse error("No document model for current buffer")

  def rendering(view: View = null): JEdit_Rendering =
    maybe_rendering(view) getOrElse error("No document view for current text area")


  /* plugin instance */

  @volatile var _plugin: Main_Plugin = null

  def get_plugin: Option[Main_Plugin] = Option(_plugin)

  def plugin: Main_Plugin =
    get_plugin.getOrElse(error("Uninitialized Isabelle/jEdit plugin"))

  def title: String =
    proper_string(Isabelle_System.getenv("ISABELLE_IDENTIFIER")).getOrElse("Isabelle") +
      (get_plugin match {
        case Some(main) => "/" + main.session.resources.session_base.session_name
        case None => ""
      })

  def options: Options =
    get_plugin match {
      case Some(pide) => pide.options.value
      case None => Options.defaults
    }

  def session: JEdit_Session = plugin.session
  def resources: JEdit_Resources = session.resources

  object editor extends JEdit_Editor
}

class Main_Plugin extends EBPlugin {
  /* options */

  private lazy val initial_options: Options = Options.init()

  private lazy val more_options: List[Options.Spec] =
    Library.space_explode('\u000b', Isabelle_System.getenv("JEDIT_ISABELLE_OPTIONS"))
      .map(Options.Spec.make)

  lazy val startup_options: Options = initial_options ++ more_options

  private var _options: JEdit_Options = null
  private def init_options(): Unit = {
    _options = new JEdit_Options(startup_options)
  }
  def options: JEdit_Options = _options


  /* session */

  private var _session: JEdit_Session = null
  private def init_session(): Unit = {
    _session =
      new JEdit_Session(options.value) {
        override def deps_changed(): Unit = delay_load.invoke()
        override def syntax_changed(names: List[Document.Node.Name]): Unit =
          GUI_Thread.later { Document_Model.syntax_changed(names) }
      }
  }
  def session: JEdit_Session = _session


  /* misc support */

  val completion_history = new Completion.History_Variable
  val spell_checker = new Spell_Checker_Variable
  val navigator = new Isabelle_Navigator


  /* theory files */

  private lazy val delay_init: Delay =
    Delay.last(PIDE.session.load_delay, gui = true) { init_models() }

  private lazy val delay_load: Delay =
    Delay.last(session.load_delay, gui = true) {
      if (JEdit_Options.continuous_checking()) {
        if (!PerspectiveManager.isPerspectiveEnabled ||
            JEdit_Lib.jedit_buffers().exists(_.isLoading)) delay_load.invoke()
        else if (delay_load_activated()) delay_load_body()
        else delay_load.invoke()
      }
    }

  private val delay_load_active = Synchronized(false)
  private def delay_load_finished(): Unit = delay_load_active.change(_ => false)
  private def delay_load_activated(): Boolean =
    delay_load_active.guarded_access(a => Some((!a, true)))

  private def delay_load_body(): Unit = {
    val required_files = {
      val models = Document_Model.get_models_map()

      val thy_files =
        session.resources.resolve_dependencies(models.values, PIDE.editor.document_required())

      val aux_files =
        if (session.auto_resolve) {
          session.stable_tip_version(models.values) match {
            case Some(version) => session.resources.undefined_blobs(version)
            case None => delay_load.invoke(); Nil
          }
        }
        else Nil

      (thy_files ::: aux_files).filterNot(models.keySet)
    }
    if (required_files.nonEmpty) {
      try {
        Isabelle_Thread.fork(name = "resolve_dependencies") {
          val loaded_files =
            for {
              name <- required_files
              text <- session.resources.read_file_content(name)
            } yield (name, text)

          GUI_Thread.later {
            try {
              Document_Model.provide_files(session, loaded_files)
              delay_init.invoke()
            }
            finally { delay_load_finished() }
          }
        }
      }
      catch { case _: Throwable => delay_load_finished() }
    }
    else delay_load_finished()
  }

  private def file_watcher_action(changed: Set[JFile]): Unit =
    if (Document_Model.sync_files(changed)) PIDE.editor.invoke_generated()

  lazy val file_watcher: File_Watcher =
    File_Watcher(file_watcher_action, session.load_delay)


  /* session phase */

  val session_phase_changed: Session.Consumer[Session.Phase] = Session.Consumer("Isabelle/jEdit") {
    case Session.Terminated(result) if !result.ok =>
      GUI_Thread.later {
        GUI.error_dialog(jEdit.getActiveView, "Prover process terminated with error",
          "Isabelle Syslog", GUI.scrollable_text(session.syslog.content()))
      }

    case Session.Ready if !shutting_down.value =>
      init_models()

      if (!JEdit_Options.continuous_checking()) {
        GUI_Thread.later {
          val answer =
            GUI.confirm_dialog(jEdit.getActiveView,
              "Continuous checking of PIDE document",
              JOptionPane.YES_NO_OPTION,
              "Continuous checking is presently disabled:",
              "editor buffers will remain inactive!",
              "Enable continuous checking now?")
          if (answer == 0) JEdit_Options.continuous_checking.set()
        }
      }

      delay_load.invoke()

    case Session.Shutdown =>
      GUI_Thread.later {
        delay_load.revoke()
        delay_init.revoke()
        PIDE.editor.shutdown()
        exit_models(JEdit_Lib.jedit_buffers().toList)
      }

    case _ =>
  }


  /* document model and view */

  def exit_models(buffers: List[Buffer]): Unit = {
    GUI_Thread.now {
      buffers.foreach(buffer =>
        JEdit_Lib.buffer_lock(buffer) {
          JEdit_Lib.jedit_text_areas(buffer).foreach(Document_View.exit)
          Document_Model.exit(buffer)
        })
      }
  }

  def init_models(): Unit = {
    GUI_Thread.now {
      PIDE.editor.flush()

      for {
        buffer <- JEdit_Lib.jedit_buffers()
        if buffer != null && !buffer.getBooleanProperty(Buffer.GZIPPED)
      } {
        if (buffer.isLoaded) {
          JEdit_Lib.buffer_lock(buffer) {
            val node_name = session.resources.node_name(buffer)
            val model = Document_Model.init(session, node_name, buffer)
            for {
              text_area <- JEdit_Lib.jedit_text_areas(buffer)
              if !Document_View.get(text_area).map(_.model).contains(model)
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
        Document_Model.get_model(buffer) match {
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

  private def init_editor(view: View): Unit = {
    Keymap_Merge.check_dialog(view)
    Session_Build.check_dialog(view)
  }

  private def init_title(view: View): Unit = {
    val marker = "\u200B"
    val old_title = view.getViewConfig.title
    if (old_title == null || old_title.startsWith(marker)) {
      view.setUserTitle(marker + PIDE.title)
    }
  }

  override def handleMessage(message: EBMessage): Unit = {
    GUI_Thread.assert {}

    if (startup_failure.isDefined && !startup_notified) {
      message match {
        case _: EditorStarted =>
          GUI.error_dialog(null, "Isabelle plugin startup failure",
            GUI.scrollable_text(Exn.message(startup_failure.get)),
            "Prover IDE inactive!")
          startup_notified = true
        case _ =>
      }
    }

    if (startup_failure.isEmpty) {
      message match {
        case _: EditorStarted =>
          val view = jEdit.getActiveView

          try { session.resources.session_background.check_errors }
          catch {
            case ERROR(msg) =>
              GUI.warning_dialog(view,
                "Bad session structure: may cause problems with theory imports",
                GUI.scrollable_text(msg))
          }

          jEdit.propertiesChanged()

          if (view != null) {
            init_editor(view)

            PIDE.editor.hyperlink_position(Document.Snapshot.init,
              JEdit_Session.logic_root(options.value), focus = true).foreach(_.follow(view))
          }

        case msg: ViewUpdate =>
          val what = msg.getWhat
          val view = msg.getView
          what match {
            case ViewUpdate.CREATED if view != null => init_title(view)
            case _ =>
          }

        case msg: BufferUpdate =>
          val what = msg.getWhat
          val buffer = msg.getBuffer
          val view = msg.getView
          val view_edit_pane = if (view == null) null else view.getEditPane

          what match {
            case BufferUpdate.LOAD_STARTED | BufferUpdate.CLOSING if buffer != null =>
              exit_models(List(buffer))
              PIDE.editor.invoke_generated()
            case BufferUpdate.PROPERTIES_CHANGED | BufferUpdate.LOADED if session.is_ready =>
              delay_init.invoke()
              delay_load.invoke()
            case _ =>
          }

          if (buffer != null && !buffer.isUntitled) {
            what match {
              case BufferUpdate.CREATED => navigator.init(Set(buffer))
              case BufferUpdate.CLOSED => navigator.exit(Set(buffer))
              case _ =>
            }
          }

        case msg: EditPaneUpdate =>
          val what = msg.getWhat
          val edit_pane = msg.getEditPane
          val buffer = if (edit_pane == null) null else edit_pane.getBuffer
          val text_area = if (edit_pane == null) null else edit_pane.getTextArea

          if (buffer != null && text_area != null) {
            if (what == EditPaneUpdate.BUFFER_CHANGED || what == EditPaneUpdate.CREATED) {
              if (session.is_ready) init_view(buffer, text_area)
            }

            if (what == EditPaneUpdate.BUFFER_CHANGING || what == EditPaneUpdate.DESTROYED) {
              Isabelle.dismissed_popups(text_area.getView)
              exit_view(buffer, text_area)
            }

            if (what == EditPaneUpdate.CREATED) Completion_Popup.Text_Area.init(text_area)

            if (what == EditPaneUpdate.DESTROYED) Completion_Popup.Text_Area.exit(text_area)
          }

          if (msg.isInstanceOf[PositionChanging]) {
            JEdit_Mouse_Handler.jump(edit_pane)
            navigator.record(Isabelle_Navigator.Pos(edit_pane))
          }

        case _: PropertiesChanged =>
          for {
            view <- JEdit_Lib.jedit_views()
            edit_pane <- JEdit_Lib.jedit_edit_panes(view)
          } {
            val buffer = edit_pane.getBuffer
            val text_area = edit_pane.getTextArea
            if (buffer != null && text_area != null) init_view(buffer, text_area)
          }

          spell_checker.update(options.value)
          session.update_options(options.value)

        case _ =>
      }
    }
  }


  /* mode provider */

  private var orig_mode_provider: ModeProvider = null
  private var pide_mode_provider: ModeProvider = null

  def init_mode_provider(): Unit = {
    orig_mode_provider = ModeProvider.instance
    if (orig_mode_provider.isInstanceOf[ModeProvider]) {
      pide_mode_provider = new Token_Markup.Mode_Provider(orig_mode_provider)
      ModeProvider.instance = pide_mode_provider
    }
  }

  def exit_mode_provider(): Unit = {
    if (ModeProvider.instance == pide_mode_provider)
      ModeProvider.instance = orig_mode_provider
  }


  /* HTTP server */

  val http_root: String = "/" + UUID.random_string()

  val http_server: HTTP.Server =
    HTTP.server(services = Document_Model.Preview_Service :: HTTP.isabelle_services)


  /* start and stop */

  private val shutting_down = Synchronized(false)

  override def start(): Unit = {
    /* strict initialization */

    init_options()
    init_session()
    PIDE._plugin = this


    /* non-strict initialization */

    try {
      completion_history.load()
      spell_checker.update(options.value)

      JEdit_Lib.jedit_views().foreach(init_title)
      navigator.init(JEdit_Lib.jedit_buffers())

      Syntax_Style.set_extender(Syntax_Style.Main_Extender)
      init_mode_provider()
      JEdit_Lib.jedit_text_areas().foreach(Completion_Popup.Text_Area.init)

      http_server.start()

      startup_failure = None
    }
    catch {
      case exn: Throwable =>
        startup_failure = Some(exn)
        startup_notified = false
        Log.log(Log.ERROR, this, exn)
    }

    shutting_down.change(_ => false)

    val view = jEdit.getActiveView
    if (view != null) init_editor(view)
  }

  override def stop(): Unit = {
    http_server.stop()

    Syntax_Style.set_extender(Syntax_Style.Base_Extender)

    exit_mode_provider()
    JEdit_Lib.jedit_text_areas().foreach(Completion_Popup.Text_Area.exit)

    if (startup_failure.isEmpty) {
      val save_options =
        more_options.foldLeft(options.value) {
          case (opts, opt) => opts + initial_options.spec(opt.name)
        }
      save_options.save_prefs()
      completion_history.value.save()
    }

    exit_models(JEdit_Lib.jedit_buffers().toList)

    shutting_down.change(_ => true)
    session.stop()
    file_watcher.shutdown()
    PIDE.editor.shutdown()

    Document_Model.reset()
  }
}
