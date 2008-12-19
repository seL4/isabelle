/*
 * Main Isabelle/jEdit plugin setup
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit

import java.awt.Font
import java.io.{ FileInputStream, IOException }
import javax.swing.JScrollPane

import isabelle.utils.EventSource

import isabelle.prover.{ Prover, Command }

import isabelle.IsabelleSystem

import scala.collection.mutable.HashMap

import org.gjt.sp.jedit.{ jEdit, EBMessage, EBPlugin, Buffer, EditPane, ServiceManager, View }
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.textarea.JEditTextArea
import org.gjt.sp.jedit.msg.{ EditPaneUpdate, PropertiesChanged }

object Plugin {
  val NAME = "Isabelle"
  val OPTION_PREFIX = "options.isabelle."
  val VFS_PREFIX = "isabelle:"
  
  def property(name : String) = jEdit.getProperty(OPTION_PREFIX + name)
  def property(name : String, value : String) = 
    jEdit.setProperty(OPTION_PREFIX + name, value)
  
  var plugin : Plugin = null
  def prover(buffer : JEditBuffer) = plugin.prover_setup(buffer).get.prover
  def prover_setup(buffer : JEditBuffer) = plugin.prover_setup(buffer).get

}

class Plugin extends EBPlugin {
  import Plugin._

  private val mapping = new HashMap[JEditBuffer, ProverSetup]

  var viewFont : Font = null
  val viewFontChanged = new EventSource[Font]

  def install(view : View) {
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

  def uninstall(view : View) {
    val buffer = view.getBuffer
    mapping.removeKey(buffer) match{
      case None => System.err.println("No Plugin installed on this Buffer")
      case Some(proversetup) =>
        proversetup.deactivate
    }
  }

  def prover_setup (buffer : JEditBuffer) : Option[ProverSetup] = mapping.get(buffer)
  def is_active (buffer : JEditBuffer) = mapping.get(buffer) match { case None => false case _ => true}
  
  override def handleMessage(msg : EBMessage) = msg match {
    case epu : EditPaneUpdate => epu.getWhat() match {
      case EditPaneUpdate.BUFFER_CHANGED =>
        mapping get epu.getEditPane.getBuffer match {
          //only activate 'isabelle'-buffers!
          case None =>
          case Some(prover_setup) => 
            prover_setup.theory_view.activate
            val dockable = epu.getEditPane.getView.getDockableWindowManager.getDockable("Isabelle_output")
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

  def setFont(path : String, size : Float) {
    try {
      val fontStream = new FileInputStream(path)
      val font = Font.createFont(Font.TRUETYPE_FONT, fontStream)
      viewFont = font.deriveFont(Font.PLAIN, size)

      viewFontChanged.fire(viewFont)
    }
    catch {
      case e : IOException =>
    }
  }
  
  override def start() {
    plugin = this
    
    if (property("font-path") != null && property("font-size") != null)
      try {
        setFont(property("font-path"), property("font-size").toFloat)
      }
      catch {
        case e : NumberFormatException =>
      }
  }
  
  override def stop() {
    // TODO: implement cleanup
  }
}
