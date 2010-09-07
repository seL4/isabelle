/*  Title:      Tools/jEdit/src/jedit/plugin.scala
    Author:     Makarius

Main Isabelle/jEdit plugin setup.
*/

package isabelle.jedit


import isabelle._

import java.io.{FileInputStream, IOException}
import java.awt.Font
import javax.swing.JTextArea

import scala.collection.mutable

import org.gjt.sp.jedit.{jEdit, EBMessage, EBPlugin, Buffer, EditPane, ServiceManager, View}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea}
import org.gjt.sp.jedit.msg.{BufferUpdate, EditPaneUpdate, PropertiesChanged}
import org.gjt.sp.jedit.gui.DockableWindowManager


object Isabelle
{
  /* plugin instance */

  var system: Isabelle_System = null
  var session: Session = null


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


  /* font */

  def font_family(): String = jEdit.getProperty("view.font")

  def font_size(): Float =
    (jEdit.getIntegerProperty("view.fontsize", 16) *
      Int_Property("relative-font-size", 100)).toFloat / 100


  /* text area ranges */

  case class Gfx_Range(val x: Int, val y: Int, val length: Int)

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

  def tooltip_dismiss_delay(): Int =
    Int_Property("tooltip-dismiss-delay", 8000) max 500

  def setup_tooltips()
  {
    Swing_Thread.now {
      val manager = javax.swing.ToolTipManager.sharedInstance
      manager.setDismissDelay(tooltip_dismiss_delay())
    }
  }


  /* settings */

  def default_logic(): String =
  {
    val logic = system.getenv("JEDIT_LOGIC")
    if (logic != "") logic
    else system.getenv_strict("ISABELLE_LOGIC")
  }

  def isabelle_args(): List[String] =
  {
    val modes = system.getenv("JEDIT_PRINT_MODE").split(",").toList.map("-m" + _)
    val logic = {
      val logic = Property("logic")
      if (logic != null && logic != "") logic
      else default_logic()
    }
    modes ++ List(logic)
  }


  /* main jEdit components */

  def jedit_buffers(): Iterator[Buffer] = jEdit.getBuffers().iterator

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

  def swing_buffer_lock[A](buffer: JEditBuffer)(body: => A): A =
    Swing_Thread.now { buffer_lock(buffer) { body } }


  /* dockable windows */

  private def wm(view: View): DockableWindowManager = view.getDockableWindowManager

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


  /* manage prover */  // FIXME async!?

  private def prover_started(view: View): Boolean =
  {
    val timeout = Int_Property("startup-timeout") max 1000
    session.started(timeout, Isabelle.isabelle_args()) match {
      case Some(err) =>
        val text = new JTextArea(err); text.setEditable(false)
        Library.error_dialog(view, null, "Failed to start Isabelle process", text)
        false
      case None => true
    }
  }


  /* activation */

  def activate_buffer(view: View, buffer: Buffer)
  {
    if (prover_started(view)) {
      // FIXME proper error handling
      val (_, thy_name) = Thy_Header.split_thy_path(Isabelle.system.posix_path(buffer.getPath))

      val model = Document_Model.init(session, buffer, thy_name)
      for (text_area <- jedit_text_areas(buffer))
        Document_View.init(model, text_area)
    }
  }

  def deactivate_buffer(buffer: Buffer)
  {
    session.stop()  // FIXME not yet

    for (text_area <- jedit_text_areas(buffer))
      Document_View.exit(text_area)
    Document_Model.exit(buffer)
  }

  def switch_active(view: View) =
  {
    val buffer = view.getBuffer
    if (Document_Model(buffer).isDefined) deactivate_buffer(buffer)
    else activate_buffer(view, buffer)
  }

  def is_active(view: View): Boolean =
    Document_Model(view.getBuffer).isDefined
}


class Plugin extends EBPlugin
{
  /* main plugin plumbing */

  override def handleMessage(message: EBMessage)
  {
    message match {
      case msg: BufferUpdate
        if msg.getWhat == BufferUpdate.PROPERTIES_CHANGED =>
        Document_Model(msg.getBuffer) match {
          case Some(model) => model.refresh()
          case _ =>
        }

      case msg: EditPaneUpdate =>
        val edit_pane = msg.getEditPane
        val buffer = edit_pane.getBuffer
        val text_area = edit_pane.getTextArea

        def init_view()
        {
          Document_Model(buffer) match {
            case Some(model) => Document_View.init(model, text_area)
            case None =>
          }
        }
        def exit_view()
        {
          if (Document_View(text_area).isDefined)
            Document_View.exit(text_area)
        }
        msg.getWhat match {
          case EditPaneUpdate.BUFFER_CHANGED => exit_view(); init_view()
          case EditPaneUpdate.CREATED => init_view()
          case EditPaneUpdate.DESTROYED => exit_view()
          case _ =>
        }

      case msg: PropertiesChanged =>
        Swing_Thread.now {
          for (text_area <- Isabelle.jedit_text_areas if Document_View(text_area).isDefined)
            Document_View(text_area).get.extend_styles()

          Isabelle.setup_tooltips()
        }

        Isabelle.session.global_settings.event(Session.Global_Settings)

      case _ =>
    }
  }

  override def start()
  {
    Isabelle.system = new Isabelle_System
    Isabelle.system.install_fonts()
    Isabelle.session = new Session(Isabelle.system)  // FIXME dialog!?

    Isabelle.setup_tooltips()
  }

  override def stop()  // FIXME fragile
  {
    Isabelle.session.stop()  // FIXME dialog!?
    Isabelle.session = null
  }
}
