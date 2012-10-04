/*  Title:      Tools/jEdit/src/plugin.scala
    Author:     Makarius

Main Isabelle/jEdit plugin setup.
*/

package isabelle.jedit


import isabelle._

import javax.swing.JOptionPane

import scala.swing.{ListView, ScrollPane}

import org.gjt.sp.jedit.{jEdit, EBMessage, EBPlugin, Buffer, View}
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea}
import org.gjt.sp.jedit.syntax.{Token => JEditToken, ModeProvider}
import org.gjt.sp.jedit.msg.{EditorStarted, BufferUpdate, EditPaneUpdate, PropertiesChanged}
import org.gjt.sp.jedit.gui.DockableWindowManager

import org.gjt.sp.util.SyntaxUtilities

import scala.actors.Actor._


object Isabelle
{
  /* plugin instance */

  val options = new JEdit_Options

  @volatile var startup_failure: Option[Throwable] = None
  @volatile var startup_notified = false

  @volatile var plugin: Plugin = null
  @volatile var session: Session = new Session(new JEdit_Thy_Load(Set.empty, Outer_Syntax.empty))

  def thy_load(): JEdit_Thy_Load =
    session.thy_load.asInstanceOf[JEdit_Thy_Load]

  def get_recent_syntax(): Option[Outer_Syntax] =
  {
    val current_session = session
    if (current_session.recent_syntax == Outer_Syntax.empty) None
    else Some(current_session.recent_syntax)
  }


  /* font */

  def font_family(): String = jEdit.getProperty("view.font")

  def font_size(scale: String): Float =
    (jEdit.getIntegerProperty("view.fontsize", 16) * options.real(scale)).toFloat


  /* tooltip delay */

  private val tooltip_lb = Time.seconds(0.5)
  private val tooltip_ub = Time.seconds(60.0)
  def tooltip_dismiss_delay(): Time =
    Time.seconds(options.real("jedit_tooltip_dismiss_delay")) max tooltip_lb min tooltip_ub

  def setup_tooltips()
  {
    Swing_Thread.now {
      val manager = javax.swing.ToolTipManager.sharedInstance
      manager.setDismissDelay(tooltip_dismiss_delay().ms.toInt)
    }
  }


  /* document model and view */

  def document_model(buffer: Buffer): Option[Document_Model] = Document_Model(buffer)
  def document_view(text_area: JEditTextArea): Option[Document_View] = Document_View(text_area)

  def document_views(buffer: Buffer): List[Document_View] =
    for {
      text_area <- JEdit_Lib.jedit_text_areas(buffer).toList
      doc_view = document_view(text_area)
      if doc_view.isDefined
    } yield doc_view.get

  def exit_model(buffer: Buffer)
  {
    JEdit_Lib.swing_buffer_lock(buffer) {
      JEdit_Lib.jedit_text_areas(buffer).foreach(Document_View.exit)
      Document_Model.exit(buffer)
    }
  }

  def init_model(buffer: Buffer)
  {
    JEdit_Lib.swing_buffer_lock(buffer) {
      val opt_model =
        JEdit_Lib.buffer_node_name(buffer) match {
          case Some(node_name) =>
            document_model(buffer) match {
              case Some(model) if model.name == node_name => Some(model)
              case _ => Some(Document_Model.init(session, buffer, node_name))
            }
          case None => None
        }
      if (opt_model.isDefined) {
        for (text_area <- JEdit_Lib.jedit_text_areas(buffer)) {
          if (document_view(text_area).map(_.model) != opt_model)
            Document_View.init(opt_model.get, text_area)
        }
      }
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


  /* dockable windows */

  private def wm(view: View): DockableWindowManager = view.getDockableWindowManager

  def docked_session(view: View): Option[Session_Dockable] =
    wm(view).getDockableWindow("isabelle-session") match {
      case dockable: Session_Dockable => Some(dockable)
      case _ => None
    }

  def docked_output(view: View): Option[Output_Dockable] =
    wm(view).getDockableWindow("isabelle-output") match {
      case dockable: Output_Dockable => Some(dockable)
      case _ => None
    }

  def docked_raw_output(view: View): Option[Raw_Output_Dockable] =
    wm(view).getDockableWindow("isabelle-raw-output") match {
      case dockable: Raw_Output_Dockable => Some(dockable)
      case _ => None
    }

  def docked_protocol(view: View): Option[Protocol_Dockable] =
    wm(view).getDockableWindow("isabelle-protocol") match {
      case dockable: Protocol_Dockable => Some(dockable)
      case _ => None
    }


  /* convenience actions */

  private def user_input(text_area: JEditTextArea, s1: String, s2: String = "")
  {
    s1.foreach(text_area.userInput(_))
    s2.foreach(text_area.userInput(_))
    s2.foreach(_ => text_area.goToPrevCharacter(false))
  }

  def input_sub(text_area: JEditTextArea): Unit = user_input(text_area, Symbol.sub_decoded)
  def input_sup(text_area: JEditTextArea): Unit = user_input(text_area, Symbol.sup_decoded)
  def input_isub(text_area: JEditTextArea): Unit = user_input(text_area, Symbol.isub_decoded)
  def input_isup(text_area: JEditTextArea): Unit = user_input(text_area, Symbol.isup_decoded)
  def input_bsub(text_area: JEditTextArea): Unit = user_input(text_area, Symbol.bsub_decoded, Symbol.esub_decoded)
  def input_bsup(text_area: JEditTextArea): Unit = user_input(text_area, Symbol.bsup_decoded, Symbol.esup_decoded)
  def input_bold(text_area: JEditTextArea): Unit = user_input(text_area, Symbol.bold_decoded)

  def check_buffer(buffer: Buffer)
  {
    document_model(buffer) match {
      case None =>
      case Some(model) => model.full_perspective()
    }
  }

  def cancel_execution() { session.cancel_execution() }
}


class Plugin extends EBPlugin
{
  /* theory files */

  private lazy val delay_load =
    Swing_Thread.delay_last(Time.seconds(Isabelle.options.real("editor_load_delay")))
    {
      val view = jEdit.getActiveView()

      val buffers = JEdit_Lib.jedit_buffers().toList
      if (buffers.forall(_.isLoaded)) {
        def loaded_buffer(name: String): Boolean =
          buffers.exists(buffer => JEdit_Lib.buffer_name(buffer) == name)

        val thys =
          for (buffer <- buffers; model <- Isabelle.document_model(buffer))
            yield model.name

        val thy_info = new Thy_Info(Isabelle.thy_load)
        // FIXME avoid I/O in Swing thread!?!
        val files = thy_info.dependencies(true, thys).deps.map(_._1.node).
          filter(file => !loaded_buffer(file) && Isabelle.thy_load.check_file(view, file))

        if (!files.isEmpty) {
          val files_list = new ListView(files.sorted)
          for (i <- 0 until files.length)
            files_list.selection.indices += i

          val answer =
            Library.confirm_dialog(view,
              "Auto loading of required files",
              JOptionPane.YES_NO_OPTION,
              "The following files are required to resolve theory imports.",
              "Reload selected files now?",
              new ScrollPane(files_list))
          if (answer == 0) {
            files.foreach(file =>
              if (files_list.selection.items.contains(file))
                jEdit.openFile(null: View, file))
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
            case Session.Failed =>
              Swing_Thread.later {
                Library.error_dialog(jEdit.getActiveView, "Prover process failure",
                    "Isabelle Syslog", Library.scrollable_text(Isabelle.session.current_syslog()))
              }

            case Session.Ready =>
              JEdit_Lib.jedit_buffers.foreach(Isabelle.init_model)
              Swing_Thread.later { delay_load.invoke() }

            case Session.Shutdown =>
              JEdit_Lib.jedit_buffers.foreach(Isabelle.exit_model)
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

    if (Isabelle.startup_failure.isDefined && !Isabelle.startup_notified) {
      message match {
        case msg: EditorStarted =>
          Library.error_dialog(null, "Isabelle plugin startup failure",
            Library.scrollable_text(Exn.message(Isabelle.startup_failure.get)),
            "Prover IDE inactive!")
          Isabelle.startup_notified = true
        case _ =>
      }
    }

    if (Isabelle.startup_failure.isEmpty) {
      message match {
        case msg: EditorStarted =>
          if (Isabelle.options.bool("jedit_auto_start"))
            Isabelle.session.start(Isabelle_Logic.session_args())

        case msg: BufferUpdate
        if msg.getWhat == BufferUpdate.LOADED || msg.getWhat == BufferUpdate.PROPERTIES_CHANGED =>
          if (Isabelle.session.is_ready) {
            val buffer = msg.getBuffer
            if (buffer != null && !buffer.isLoading) Isabelle.init_model(buffer)
            Swing_Thread.later { delay_load.invoke() }
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
              if (Isabelle.session.is_ready)
                Isabelle.init_view(buffer, text_area)
            }
            else Isabelle.exit_view(buffer, text_area)
          }

        case msg: PropertiesChanged =>
          Isabelle.setup_tooltips()
          Isabelle.session.global_options.event(Session.Global_Options)

        case _ =>
      }
    }
  }

  override def start()
  {
    try {
      Isabelle.plugin = this
      Isabelle_System.init()
      Isabelle_System.install_fonts()

      val init_options = Options.init()
      Swing_Thread.now {
        Isabelle.options.update(init_options)
        Isabelle.setup_tooltips()
      }

      SyntaxUtilities.setStyleExtender(new Token_Markup.Style_Extender)
      if (ModeProvider.instance.isInstanceOf[ModeProvider])
        ModeProvider.instance = new Token_Markup.Mode_Provider(ModeProvider.instance)

      val content = Isabelle_Logic.session_content(false)
      val thy_load = new JEdit_Thy_Load(content.loaded_theories, content.syntax)

      Isabelle.session = new Session(thy_load) {
        override def output_delay = Time.seconds(Isabelle.options.real("editor_output_delay"))
        override def reparse_limit = Isabelle.options.int("editor_reparse_limit")
      }

      Isabelle.session.phase_changed += session_manager
      Isabelle.startup_failure = None
    }
    catch {
      case exn: Throwable =>
        Isabelle.startup_failure = Some(exn)
        Isabelle.startup_notified = false
    }
  }

  override def stop()
  {
    if (Isabelle.startup_failure.isEmpty)
      Isabelle.options.value.save_prefs()

    Isabelle.session.phase_changed -= session_manager
    JEdit_Lib.jedit_buffers.foreach(Isabelle.exit_model)
    Isabelle.session.stop()
  }
}
