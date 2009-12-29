/*
 * Main Isabelle/jEdit plugin setup
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.jedit


import isabelle.proofdocument.Session

import java.io.{FileInputStream, IOException}
import java.awt.Font
import javax.swing.JScrollPane

import scala.collection.mutable

import org.gjt.sp.jedit.{jEdit, EBMessage, EBPlugin, Buffer, EditPane, ServiceManager, View}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.textarea.JEditTextArea
import org.gjt.sp.jedit.msg.{EditPaneUpdate, PropertiesChanged}


object Isabelle
{
  /* plugin instance */

  var plugin: Plugin = null
  var system: Isabelle_System = null
  var session: Session = null


  /* name */

  val NAME = "Isabelle"


  /* properties */

  val OPTION_PREFIX = "options.isabelle."

  object Property
  {
    def apply(name: String): String = jEdit.getProperty(OPTION_PREFIX + name)
    def update(name: String, value: String) = jEdit.setProperty(OPTION_PREFIX + name, value)
  }

  object Boolean_Property
  {
    def apply(name: String): Boolean = jEdit.getBooleanProperty(OPTION_PREFIX + name)
    def update(name: String, value: Boolean) = jEdit.setBooleanProperty(OPTION_PREFIX + name, value)
  }

  object Int_Property
  {
    def apply(name: String): Int = jEdit.getIntegerProperty(OPTION_PREFIX + name)
    def update(name: String, value: Int) = jEdit.setIntegerProperty(OPTION_PREFIX + name, value)
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


  /* main jEdit components */  // FIXME ownership!?

  def jedit_buffers(): Iterator[Buffer] = Iterator.fromArray(jEdit.getBuffers())

  def jedit_views(): Iterator[View] = Iterator.fromArray(jEdit.getViews())

  def jedit_text_areas(view: View): Iterator[JEditTextArea] =
    Iterator.fromArray(view.getEditPanes).map(_.getTextArea)

  def jedit_text_areas(): Iterator[JEditTextArea] =
    jedit_views().flatMap(jedit_text_areas(_))

  def jedit_text_areas(buffer: JEditBuffer): Iterator[JEditTextArea] =
    jedit_text_areas().filter(_.getBuffer == buffer)


  /* activation */

  def activate_buffer(buffer: Buffer)
  {
    session.start(Isabelle.isabelle_args())
    val model = Document_Model.init(session, buffer)
    for (text_area <- jedit_text_areas(buffer))
      Document_View.init(model, text_area)
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
    else activate_buffer(buffer)
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
        Isabelle.session.global_settings.event(Session.Global_Settings)

      case _ =>
    }
  }

  override def start()
  {
    Isabelle.plugin = this
    Isabelle.system = new Isabelle_System
    Isabelle.system.install_fonts()
    Isabelle.session = new Session(Isabelle.system)  // FIXME dialog!?
  }

  override def stop()
  {
    Isabelle.session.stop()  // FIXME dialog!?
    Isabelle.session = null
    Isabelle.system = null
    Isabelle.plugin = null
  }
}
