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

import scala.collection.mutable.HashMap

import isabelle.utils.EventSource
import isabelle.prover.{Prover, Command}
import isabelle.{IsabelleSystem, Symbol}

import org.gjt.sp.jedit.{jEdit, EBMessage, EBPlugin, Buffer, EditPane, ServiceManager, View}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.textarea.JEditTextArea
import org.gjt.sp.jedit.msg.{EditPaneUpdate, PropertiesChanged}


object Isabelle {
  // name
  val NAME = "Isabelle"
  val OPTION_PREFIX = "options.isabelle."
  val VFS_PREFIX = "isabelle:"

  // properties
  def property(name: String) = jEdit.getProperty(OPTION_PREFIX + name)
  def property(name: String, value: String) = 
    jEdit.setProperty(OPTION_PREFIX + name, value)


  // Isabelle system
  var system: IsabelleSystem = null
  var symbols: Symbol.Interpretation = null


  // plugin instance
  var plugin: Plugin = null

  // provers
  def prover(buffer: JEditBuffer) = plugin.prover_setup(buffer).get.prover
  def prover_setup(buffer: JEditBuffer) = plugin.prover_setup(buffer).get
}


class Plugin extends EBPlugin {

  // Isabelle font

  var font: Font = null
  val font_changed = new EventSource[Font]

  def set_font(path: String, size: Float) {
    try {
      font = Font.createFont(Font.TRUETYPE_FONT, new FileInputStream(path)).
        deriveFont(Font.PLAIN, size)
      font_changed.fire(font)
    }
    catch {
      case e: IOException =>
    }
  }


  // mapping buffer <-> prover

  private val mapping = new HashMap[JEditBuffer, ProverSetup]

  def install(view: View) {
    val buffer = view.getBuffer
    mapping.get(buffer) match{
      case None =>{
          val prover_setup = new ProverSetup(buffer)
          mapping.update(buffer, prover_setup)
          prover_setup.activate(view)
      }
      case _ => System.err.println("Already installed plugin on Buffer")
    }
  }

  def uninstall(view: View) {
    val buffer = view.getBuffer
    mapping.removeKey(buffer) match{
      case None => System.err.println("No Plugin installed on this Buffer")
      case Some(proversetup) =>
        proversetup.deactivate
    }
  }

  def prover_setup(buffer: JEditBuffer): Option[ProverSetup] = mapping.get(buffer)
  def is_active(buffer: JEditBuffer) = mapping.isDefinedAt(buffer)

  
  // main plugin plumbing

  override def handleMessage(msg: EBMessage) = msg match {
    case epu: EditPaneUpdate => epu.getWhat match {
      case EditPaneUpdate.BUFFER_CHANGED =>
        mapping get epu.getEditPane.getBuffer match {
          //only activate 'isabelle'-buffers!
          case None =>
          case Some(prover_setup) => 
            prover_setup.theory_view.activate
            val dockable = epu.getEditPane.getView.getDockableWindowManager.getDockable("isabelle-output")
            if(dockable != null) {
              val output_dockable = dockable.asInstanceOf[OutputDockable]
              if(output_dockable.getComponent(0) != prover_setup.output_text_view ) {
                output_dockable.asInstanceOf[OutputDockable].removeAll
                output_dockable.asInstanceOf[OutputDockable].add(new JScrollPane(prover_setup.output_text_view))
                output_dockable.revalidate
              }
            }
        }
      case EditPaneUpdate.BUFFER_CHANGING =>
        val buffer = epu.getEditPane.getBuffer
        if(buffer != null) mapping get buffer match {
          //only deactivate 'isabelle'-buffers!
          case None =>
          case Some(prover_setup) => prover_setup.theory_view.deactivate
        }
      case _ =>
    }
    case _ =>
  }

  override def start() {
    Isabelle.system = new IsabelleSystem
    Isabelle.symbols = new Symbol.Interpretation(Isabelle.system)
    Isabelle.plugin = this
    
    if (Isabelle.property("font-path") != null && Isabelle.property("font-size") != null)
      try {
        set_font(Isabelle.property("font-path"), Isabelle.property("font-size").toFloat)
      }
      catch {
        case e: NumberFormatException =>
      }
  }
  
  override def stop() {
    // TODO: proper cleanup
    Isabelle.symbols = null
    Isabelle.system = null
    Isabelle.plugin = null
  }
}
