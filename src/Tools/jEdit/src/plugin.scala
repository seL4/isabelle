/*  Title:      Tools/jEdit/src/plugin.scala
    Author:     Makarius

Main Isabelle/jEdit plugin setup.
*/

package isabelle.jedit


import isabelle._

import java.lang.System
import java.awt.Font
import javax.swing.JOptionPane

import scala.collection.mutable
import scala.swing.{ComboBox, ListView, ScrollPane}

import org.gjt.sp.jedit.{jEdit, GUIUtilities, EBMessage, EBPlugin,
  Buffer, EditPane, ServiceManager, View}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea}
import org.gjt.sp.jedit.syntax.{Token => JEditToken, ModeProvider}
import org.gjt.sp.jedit.msg.{EditorStarted, BufferUpdate, EditPaneUpdate, PropertiesChanged}
import org.gjt.sp.jedit.gui.DockableWindowManager

import org.gjt.sp.util.SyntaxUtilities
import org.gjt.sp.util.Log

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

  def font_size(): Float =
    (jEdit.getIntegerProperty("view.fontsize", 16) *
      options.int("jedit_relative_font_size")).toFloat / 100


  /* tooltip markup */

  def tooltip(text: String): String =
    "<html><pre style=\"font-family: " + font_family() + "; font-size: " +
        options.int("jedit_tooltip_font_size").toString + "px; \">" +  // FIXME proper scaling (!?)
      HTML.encode(text) + "</pre></html>"

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


  /* icons */

  def load_icon(name: String): javax.swing.Icon =
  {
    val icon = GUIUtilities.loadIcon(name)
    if (icon.getIconWidth < 0 || icon.getIconHeight < 0)
      Log.log(Log.ERROR, icon, "Bad icon: " + name)
    icon
  }


  /* buffers */

  def swing_buffer_lock[A](buffer: JEditBuffer)(body: => A): A =
    Swing_Thread.now { buffer_lock(buffer) { body } }

  def buffer_text(buffer: JEditBuffer): String =
    buffer_lock(buffer) { buffer.getText(0, buffer.getLength) }

  def buffer_name(buffer: Buffer): String = buffer.getSymlinkPath

  def buffer_node_dummy(buffer: Buffer): Option[Document.Node.Name] =
    Some(Document.Node.Name(buffer_name(buffer), buffer.getDirectory, buffer.getName))

  def buffer_node_name(buffer: Buffer): Option[Document.Node.Name] =
  {
    val name = buffer_name(buffer)
    Thy_Header.thy_name(name).map(theory => Document.Node.Name(name, buffer.getDirectory, theory))
  }


  /* main jEdit components */

  def jedit_buffers(): Iterator[Buffer] = jEdit.getBuffers().iterator

  def jedit_buffer(name: String): Option[Buffer] =
    jedit_buffers().find(buffer => buffer_name(buffer) == name)

  def jedit_views(): Iterator[View] = jEdit.getViews().iterator

  def jedit_text_areas(view: View): Iterator[JEditTextArea] =
    view.getEditPanes().iterator.map(_.getTextArea)

  def jedit_text_areas(): Iterator[JEditTextArea] =
    jedit_views().flatMap(jedit_text_areas(_))

  def jedit_text_areas(buffer: JEditBuffer): Iterator[JEditTextArea] =
    jedit_text_areas().filter(_.getBuffer == buffer)

  def buffer_lock[A](buffer: JEditBuffer)(body: => A): A =
  {
    try { buffer.readLock(); body }
    finally { buffer.readUnlock() }
  }


  /* document model and view */

  def document_model(buffer: Buffer): Option[Document_Model] = Document_Model(buffer)
  def document_view(text_area: JEditTextArea): Option[Document_View] = Document_View(text_area)

  def document_views(buffer: Buffer): List[Document_View] =
    for {
      text_area <- jedit_text_areas(buffer).toList
      doc_view = document_view(text_area)
      if doc_view.isDefined
    } yield doc_view.get

  def exit_model(buffer: Buffer)
  {
    swing_buffer_lock(buffer) {
      jedit_text_areas(buffer).foreach(Document_View.exit)
      Document_Model.exit(buffer)
    }
  }

  def init_model(buffer: Buffer)
  {
    swing_buffer_lock(buffer) {
      val opt_model =
        buffer_node_name(buffer) match {
          case Some(node_name) =>
            document_model(buffer) match {
              case Some(model) if model.name == node_name => Some(model)
              case _ => Some(Document_Model.init(session, buffer, node_name))
            }
          case None => None
        }
      if (opt_model.isDefined) {
        for (text_area <- jedit_text_areas(buffer)) {
          if (document_view(text_area).map(_.model) != opt_model)
            Document_View.init(opt_model.get, text_area)
        }
      }
    }
  }

  def init_view(buffer: Buffer, text_area: JEditTextArea)
  {
    swing_buffer_lock(buffer) {
      document_model(buffer) match {
        case Some(model) => Document_View.init(model, text_area)
        case None =>
      }
    }
  }

  def exit_view(buffer: Buffer, text_area: JEditTextArea)
  {
    swing_buffer_lock(buffer) {
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


  /* logic image */

  def default_logic(): String =
  {
    val logic = Isabelle_System.getenv("JEDIT_LOGIC")
    if (logic != "") logic
    else Isabelle_System.getenv_strict("ISABELLE_LOGIC")
  }

  class Logic_Entry(val name: String, val description: String)
  {
    override def toString = description
  }

  def logic_selector(logic: String): ComboBox[Logic_Entry] =
  {
    val entries =
      new Logic_Entry("", "default (" + default_logic() + ")") ::
        Isabelle_System.find_logics().map(name => new Logic_Entry(name, name))
    val component = new ComboBox(entries)
    entries.find(_.name == logic) match {
      case None =>
      case Some(entry) => component.selection.item = entry
    }
    component.tooltip = "Isabelle logic image"
    component
  }

  def session_args(): List[String] =
  {
    val modes = space_explode(',', Isabelle_System.getenv("JEDIT_PRINT_MODE")).map("-m" + _)
    val logic =
      Isabelle.options.string("jedit_logic") match {
        case "" => Isabelle.default_logic()
        case logic => logic
      }
    modes ::: List(logic)
  }

  def session_content(inlined_files: Boolean): Build.Session_Content =
  {
    val dirs = Path.split(Isabelle_System.getenv("JEDIT_SESSION_DIRS"))
    val name = Path.explode(session_args().last).base.implode  // FIXME more robust
    Build.session_content(inlined_files, dirs, name).check_errors
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
    Swing_Thread.delay_last(Isabelle.session.load_delay)
    {
      val view = jEdit.getActiveView()

      val buffers = Isabelle.jedit_buffers().toList
      if (buffers.forall(_.isLoaded)) {
        def loaded_buffer(name: String): Boolean =
          buffers.exists(buffer => Isabelle.buffer_name(buffer) == name)

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
              Isabelle.jedit_buffers.foreach(Isabelle.init_model)
              Swing_Thread.later { delay_load.invoke() }

            case Session.Shutdown =>
              Isabelle.jedit_buffers.foreach(Isabelle.exit_model)
              Swing_Thread.later { delay_load.revoke() }

            case _ =>
          }
        case bad => System.err.println("session_manager: ignoring bad message " + bad)
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
            Isabelle.session.start(Isabelle.session_args())

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
          Isabelle.session.global_settings.event(Session.Global_Settings)

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

      val content = Isabelle.session_content(false)
      val thy_load = new JEdit_Thy_Load(content.loaded_theories, content.syntax)
      Isabelle.session = new Session(thy_load)

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
    Isabelle.jedit_buffers.foreach(Isabelle.exit_model)
    Isabelle.session.stop()
  }
}
