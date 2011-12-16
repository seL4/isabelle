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

  var plugin: Plugin = null
  var session: Session = null

  val thy_load = new JEdit_Thy_Load
  val thy_info = new Thy_Info(thy_load)


  /* properties */

  val OPTION_PREFIX = "options.isabelle."

  object Property
  {
    def apply(name: String): String =
      jEdit.getProperty(OPTION_PREFIX + name)
    def apply(name: String, default: String): String =
      jEdit.getProperty(OPTION_PREFIX + name, default)
    def update(name: String, value: String) =
      jEdit.setProperty(OPTION_PREFIX + name, value)
  }

  object Boolean_Property
  {
    def apply(name: String): Boolean =
      jEdit.getBooleanProperty(OPTION_PREFIX + name)
    def apply(name: String, default: Boolean): Boolean =
      jEdit.getBooleanProperty(OPTION_PREFIX + name, default)
    def update(name: String, value: Boolean) =
      jEdit.setBooleanProperty(OPTION_PREFIX + name, value)
  }

  object Int_Property
  {
    def apply(name: String): Int =
      jEdit.getIntegerProperty(OPTION_PREFIX + name)
    def apply(name: String, default: Int): Int =
      jEdit.getIntegerProperty(OPTION_PREFIX + name, default)
    def update(name: String, value: Int) =
      jEdit.setIntegerProperty(OPTION_PREFIX + name, value)
  }

  object Double_Property
  {
    def apply(name: String): Double =
      jEdit.getDoubleProperty(OPTION_PREFIX + name, 0.0)
    def apply(name: String, default: Double): Double =
      jEdit.getDoubleProperty(OPTION_PREFIX + name, default)
    def update(name: String, value: Double) =
      jEdit.setDoubleProperty(OPTION_PREFIX + name, value)
  }

  object Time_Property
  {
    def apply(name: String): Time =
      Time.seconds(Double_Property(name))
    def apply(name: String, default: Time): Time =
      Time.seconds(Double_Property(name, default.seconds))
    def update(name: String, value: Time) =
      Double_Property.update(name, value.seconds)
  }


  /* font */

  def font_family(): String = jEdit.getProperty("view.font")

  def font_size(): Float =
    (jEdit.getIntegerProperty("view.fontsize", 16) *
      Int_Property("relative-font-size", 100)).toFloat / 100


  /* text area ranges */

  sealed case class Gfx_Range(val x: Int, val y: Int, val length: Int)

  def gfx_range(text_area: TextArea, range: Text.Range): Option[Gfx_Range] =
  {
    val p = text_area.offsetToXY(range.start)
    val q = text_area.offsetToXY(range.stop)
    if (p != null && q != null && p.y == q.y) Some(new Gfx_Range(p.x, p.y, q.x - p.x))
    else None
  }


  /* tooltip markup */

  def tooltip(text: String): String =
    "<html><pre style=\"font-family: " + font_family() + "; font-size: " +
        Int_Property("tooltip-font-size", 10).toString + "px; \">" +  // FIXME proper scaling (!?)
      HTML.encode(text) + "</pre></html>"

  private val tooltip_lb = Time.seconds(0.5)
  private val tooltip_ub = Time.seconds(60.0)
  def tooltip_dismiss_delay(): Time =
    Time_Property("tooltip-dismiss-delay", Time.seconds(8.0)) max tooltip_lb min tooltip_ub

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


  /* check JVM */

  def check_jvm()
  {
    if (!Platform.is_hotspot) {
      Library.warning_dialog(jEdit.getActiveView, "Bad Java Virtual Machine",
        "This is " + Platform.jvm_name,
        "Isabelle/jEdit requires Java Hotspot from Sun/Oracle/Apple!")
    }
  }


  /* buffers */

  def swing_buffer_lock[A](buffer: JEditBuffer)(body: => A): A =
    Swing_Thread.now { buffer_lock(buffer) { body } }

  def buffer_text(buffer: JEditBuffer): String =
    buffer_lock(buffer) { buffer.getText(0, buffer.getLength) }

  def buffer_name(buffer: Buffer): String = buffer.getSymlinkPath


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
      val doc_view = document_view(text_area)
      if doc_view.isDefined
    } yield doc_view.get

  def init_model(buffer: Buffer)
  {
    swing_buffer_lock(buffer) {
      val opt_model =
        document_model(buffer) match {
          case Some(model) => Some(model)
          case None =>
            val name = buffer_name(buffer)
            Thy_Header.thy_name(name) match {
              case Some(theory) =>
                val node_name = Document.Node.Name(name, buffer.getDirectory, theory)
                Some(Document_Model.init(session, buffer, node_name))
              case None => None
            }
        }
      if (opt_model.isDefined) {
        for (text_area <- jedit_text_areas(buffer)) {
          if (document_view(text_area).map(_.model) != opt_model)
            Document_View.init(opt_model.get, text_area)
        }
      }
    }
  }

  def exit_model(buffer: Buffer)
  {
    swing_buffer_lock(buffer) {
      jedit_text_areas(buffer).foreach(Document_View.exit)
      Document_Model.exit(buffer)
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

  def start_session()
  {
    val timeout = Time_Property("startup-timeout", Time.seconds(25)) max Time.seconds(5)
    val modes = space_explode(',', Isabelle_System.getenv("JEDIT_PRINT_MODE")).map("-m" + _)
    val logic = {
      val logic = Property("logic")
      if (logic != null && logic != "") logic
      else Isabelle.default_logic()
    }
    session.start(timeout, modes ::: List(logic))
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
      def loaded_buffer(name: String): Boolean =
        buffers.exists(buffer => Isabelle.buffer_name(buffer) == name)

      val thys =
        for (buffer <- buffers; model <- Isabelle.document_model(buffer))
          yield model.name
      val files = Isabelle.thy_info.dependencies(thys).map(_._1.node).
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
        if (answer == 0)
          for {
            file <- files
            if files_list.selection.items.contains(file)
          } jEdit.openFile(null: View, file)
      }
    }


  /* session manager */

  private val session_manager = actor {
    loop {
      react {
        case phase: Session.Phase =>
          phase match {
            case Session.Failed =>
              Swing_Thread.now {
                val text = new scala.swing.TextArea(Isabelle.session.syslog())
                text.editable = false
                Library.error_dialog(jEdit.getActiveView, "Failed to start Isabelle process", text)
              }

            case Session.Ready =>
              Isabelle.jedit_buffers.foreach(Isabelle.init_model)
              delay_load()

            case Session.Shutdown => Isabelle.jedit_buffers.foreach(Isabelle.exit_model)
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
    message match {
      case msg: EditorStarted =>
        Isabelle.check_jvm()
        if (Isabelle.Boolean_Property("auto-start"))
          Isabelle.start_session()

      case msg: BufferUpdate
      if msg.getWhat == BufferUpdate.LOADED =>
        if (Isabelle.session.is_ready) {
          val buffer = msg.getBuffer
          if (buffer != null) Isabelle.init_model(buffer)
          delay_load()
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
        Swing_Thread.now { Isabelle.setup_tooltips() }
        Isabelle.session.global_settings.event(Session.Global_Settings)

      case _ =>
    }
  }

  override def start()
  {
    Isabelle.plugin = this
    Isabelle.setup_tooltips()
    Isabelle_System.init()
    Isabelle_System.install_fonts()
    Isabelle.session = new Session(Isabelle.thy_load)
    SyntaxUtilities.setStyleExtender(new Token_Markup.Style_Extender)
    if (ModeProvider.instance.isInstanceOf[ModeProvider])
      ModeProvider.instance = new Token_Markup.Mode_Provider(ModeProvider.instance)
    Isabelle.session.phase_changed += session_manager
  }

  override def stop()
  {
    Isabelle.session.phase_changed -= session_manager
    Isabelle.jedit_buffers.foreach(Isabelle.exit_model)
    Isabelle.session.stop()
  }
}
