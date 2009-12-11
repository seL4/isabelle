/*
 * Main Isabelle/jEdit plugin setup
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.jedit


import isabelle.proofdocument.{Session, Theory_View}

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

  def cmd_args(): List[String] =
  {
    val modes = system.getenv("JEDIT_PRINT_MODE").split(",").toList.map("-m" + _)
    val logic = {
      val logic1 = Isabelle.Property("logic")
      if (logic1 != null && logic1 != "") logic1
      else {
        val logic2 = system.getenv("JEDIT_LOGIC")
        if (logic2 != "") logic2
        else system.getenv_strict("ISABELLE_LOGIC")
      }
    }
    modes ++ List(logic)
  }


  /* plugin instance */

  var plugin: Plugin = null
  var system: Isabelle_System = null
  var session: Session = null
}


class Plugin extends EBPlugin
{
  /* mapping buffer <-> theory view */

  private var mapping = Map[JEditBuffer, Theory_View]()

  private def install(view: View)
  {
    val text_area = view.getTextArea
    val buffer = view.getBuffer

 
    val theory_view = new Theory_View(Isabelle.session, text_area)   // FIXME multiple text areas!?
    mapping += (buffer -> theory_view)

    Isabelle.session.start(Isabelle.cmd_args())
    theory_view.activate()
    Isabelle.session.begin_document(buffer.getName)
  }

  private def uninstall(view: View)
  {
    val buffer = view.getBuffer
    Isabelle.session.stop()
    mapping(buffer).deactivate()
    mapping -= buffer
  }

  def switch_active(view: View) =
    if (mapping.isDefinedAt(view.getBuffer)) uninstall(view)
    else install(view)

  def theory_view(buffer: JEditBuffer): Option[Theory_View] = mapping.get(buffer)
  def is_active(buffer: JEditBuffer) = mapping.isDefinedAt(buffer)


  /* main plugin plumbing */

  override def handleMessage(message: EBMessage)
  {
    message match {
      case msg: EditPaneUpdate =>
        val buffer = msg.getEditPane.getBuffer
        msg.getWhat match {
          case EditPaneUpdate.BUFFER_CHANGED =>
            theory_view(buffer)map(_.activate)
          case EditPaneUpdate.BUFFER_CHANGING =>
            if (buffer != null)
              theory_view(buffer).map(_.deactivate)
          case _ =>
        }
      case msg: PropertiesChanged =>
        Isabelle.session.global_settings.event(())
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
