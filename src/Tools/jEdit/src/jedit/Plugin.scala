package isabelle.jedit

import java.awt.Font
import java.io.{ FileInputStream, IOException }


import isabelle.utils.EventSource

import isabelle.prover.{ Prover, Command }

import isabelle.IsabelleSystem

import org.gjt.sp.jedit.{ jEdit, EBMessage, EBPlugin, Buffer, EditPane, View }
import org.gjt.sp.jedit.msg.{ EditPaneUpdate, PropertiesChanged }

object Plugin {
  val NAME = "Isabelle"
  val OPTION_PREFIX = "options.isabelle."
  
  def property(name : String) = jEdit.getProperty(OPTION_PREFIX + name)
  def property(name : String, value : String) = 
    jEdit.setProperty(OPTION_PREFIX + name, value)
  
  var plugin : Plugin = null
}

class Plugin extends EBPlugin {
  import Plugin._
  
  val prover = new Prover()
  var theoryView : TheoryView = null
  
  var viewFont : Font = null 
  val viewFontChanged = new EventSource[Font]
  
  private var _selectedState : Command = null
  
  val stateUpdate = new EventSource[Command]
  
  def selectedState = _selectedState
  def selectedState_=(newState : Command) {
    _selectedState = newState
    stateUpdate fire newState
  }
  
  def activate(view : View) {
    val logic = property("logic")
    theoryView = new TheoryView(prover, view.getBuffer())
    prover.start(if (logic == null) logic else "HOL")
    val dir = view.getBuffer().getDirectory()
    prover.setDocument(theoryView, 
                       if (dir.startsWith("isa:")) dir.substring(4) else dir)
    TheoryView.activateTextArea(view.getTextArea())
  }
  
  override def handleMessage(msg : EBMessage) = msg match {
    case epu : EditPaneUpdate => epu.getWhat() match {
      case EditPaneUpdate.BUFFER_CHANGED =>
        TheoryView.activateTextArea(epu.getEditPane().getTextArea())

      case EditPaneUpdate.BUFFER_CHANGING =>
        TheoryView.deactivateTextArea(epu.getEditPane().getTextArea())

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
