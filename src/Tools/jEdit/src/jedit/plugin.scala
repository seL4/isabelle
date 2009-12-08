/*
 * Main Isabelle/jEdit plugin setup
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.jedit


import java.io.{FileInputStream, IOException}
import java.awt.Font
import javax.swing.JScrollPane

import scala.collection.mutable

import isabelle.proofdocument.{Command, Proof_Document, Prover}
import isabelle.Isabelle_System

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


  /* Isabelle system instance */

  var system: Isabelle_System = null
  def symbols = system.symbols
  lazy val completion = new Completion + symbols


  /* settings */

  def default_logic(): String =
  {
    val logic = Isabelle.Property("logic")
    if (logic != null) logic
    else system.getenv_strict("ISABELLE_LOGIC")
  }


  /* plugin instance */

  var plugin: Plugin = null


  /* running provers */

  def prover_setup(buffer: JEditBuffer) = plugin.prover_setup(buffer)
}


class Plugin extends EBPlugin
{
  /* event buses */

  val properties_changed = new Event_Bus[Unit]
  val raw_results = new Event_Bus[Isabelle_Process.Result]
  val state_update = new Event_Bus[Command]


  /* selected state */

  private var _selected_state: Command = null
  def selected_state = _selected_state
  def selected_state_=(state: Command) { _selected_state = state; state_update.event(state) }


  /* mapping buffer <-> prover */

  private val mapping = new mutable.HashMap[JEditBuffer, Prover_Setup]

  private def install(view: View)
  {
    val buffer = view.getBuffer
    val prover_setup = new Prover_Setup(buffer)
    mapping.update(buffer, prover_setup)
    prover_setup.activate(view)
  }

  private def uninstall(view: View) =
    mapping.removeKey(view.getBuffer).get.deactivate

  def switch_active(view: View) =
    if (mapping.isDefinedAt(view.getBuffer)) uninstall(view)
    else install(view)

  def prover_setup(buffer: JEditBuffer): Option[Prover_Setup] = mapping.get(buffer)
  def is_active (buffer: JEditBuffer) = mapping.isDefinedAt(buffer)


  /* main plugin plumbing */

  override def handleMessage(message: EBMessage)
  {
    message match {
      case msg: EditPaneUpdate =>
        val buffer = msg.getEditPane.getBuffer
        msg.getWhat match {
          case EditPaneUpdate.BUFFER_CHANGED =>
            (mapping get buffer) map (_.theory_view.activate)
          case EditPaneUpdate.BUFFER_CHANGING =>
            if (buffer != null)
              (mapping get buffer) map (_.theory_view.deactivate)
          case _ =>
        }
      case msg: PropertiesChanged => properties_changed.event(())
      case _ =>
    }
  }

  override def start()
  {
    Isabelle.plugin = this
    Isabelle.system = new Isabelle_System
    Isabelle.system.register_fonts()
  }

  override def stop()
  {
    // TODO: proper cleanup
    Isabelle.system = null
    Isabelle.plugin = null
  }
}
