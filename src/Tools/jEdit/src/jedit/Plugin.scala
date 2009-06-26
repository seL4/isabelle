/*
 * Main Isabelle/jEdit plugin setup
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit


import java.io.{FileInputStream, IOException}
import java.awt.Font
import javax.swing.JScrollPane

import scala.collection.mutable

import isabelle.prover.{Prover, Command}
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

  def default_logic =
  {
    val logic = Isabelle.Property("logic")
    if (logic != null) logic else Isabelle.system.getenv_strict("ISABELLE_LOGIC")
  }


  /* plugin instance */

  var plugin: Plugin = null


  /* running provers */

  def prover_setup(buffer: JEditBuffer) = plugin.prover_setup(buffer)
}


class Plugin extends EBPlugin
{
  /* Isabelle font */

  var font: Font = null
  val font_changed = new EventBus[Font]

  def set_font(size: Int)
  {
    font = Font.createFont(Font.TRUETYPE_FONT,
        new FileInputStream(Isabelle.system.platform_path("~~/lib/fonts/IsabelleMono.ttf"))).
      deriveFont(Font.PLAIN, size max 1)
    font_changed.event(font)
  }


  /* mapping buffer <-> prover */

  private val mapping = new mutable.HashMap[JEditBuffer, ProverSetup]

  private def install(view: View)
  {
    val buffer = view.getBuffer
    val prover_setup = new ProverSetup(buffer)
    mapping.update(buffer, prover_setup)
    prover_setup.activate(view)
  }

  private def uninstall(view: View) =
    mapping.removeKey(view.getBuffer).get.deactivate

  def switch_active (view: View) =
    if (mapping.isDefinedAt(view.getBuffer)) uninstall(view)
    else install(view)

  def prover_setup(buffer: JEditBuffer): Option[ProverSetup] = mapping.get(buffer)
  def is_active (buffer: JEditBuffer) = mapping.isDefinedAt(buffer)


  /* main plugin plumbing */

  override def handleMessage(msg: EBMessage)
  {
    msg match {
      case epu: EditPaneUpdate => epu.getWhat match {
        case EditPaneUpdate.BUFFER_CHANGED =>
          mapping get epu.getEditPane.getBuffer match {
            // only activate 'isabelle' buffers
            case None =>
            case Some(prover_setup) =>
              prover_setup.theory_view.activate
              val dockable =
                epu.getEditPane.getView.getDockableWindowManager.getDockable("isabelle-output")
              if (dockable != null) {
                val output_dockable = dockable.asInstanceOf[OutputDockable]
                if (output_dockable.getComponent(0) != prover_setup.output_text_view ) {
                  output_dockable.asInstanceOf[OutputDockable].removeAll
                  output_dockable.asInstanceOf[OutputDockable].
                    add(new JScrollPane(prover_setup.output_text_view))
                  output_dockable.revalidate
                }
              }
          }
        case EditPaneUpdate.BUFFER_CHANGING =>
          val buffer = epu.getEditPane.getBuffer
          if (buffer != null) mapping get buffer match {
            // only deactivate 'isabelle' buffers
            case None =>
            case Some(prover_setup) => prover_setup.theory_view.deactivate
          }
        case _ =>
      }
      case _ =>
    }
  }

  override def start()
  {
    Isabelle.system = new Isabelle_System
    Isabelle.plugin = this
    set_font(Isabelle.Int_Property("font-size"))
  }

  override def stop()
  {
    // TODO: proper cleanup
    Isabelle.system = null
    Isabelle.plugin = null
  }

}
