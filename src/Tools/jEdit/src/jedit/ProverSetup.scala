/*
 * Independent prover sessions
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit


import isabelle.IsabelleSystem
import isabelle.utils.EventSource
import isabelle.prover.{Prover, Command}

import org.w3c.dom.Document

import org.gjt.sp.jedit.{jEdit, EBMessage, EBPlugin, Buffer, EditPane, View}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.msg.{EditPaneUpdate, PropertiesChanged}

import javax.swing.{JTextArea, JScrollPane}


class ProverSetup(buffer : JEditBuffer) {

  val prover = new Prover()
  var theory_view : TheoryView = null
  
  private var _selectedState : Command = null

  val stateUpdate = new EventSource[Command]

  def selectedState = _selectedState
  def selectedState_=(newState : Command) {
    _selectedState = newState
    stateUpdate fire newState
  }

  val output_text_view = new JTextArea("== Isabelle output ==\n")
  
  def activate(view : View) {
    val logic = Plugin.property("logic")
    prover.start(if (logic == null) logic else "HOL")
    val buffer = view.getBuffer
    val dir = buffer.getDirectory()

    theory_view = new TheoryView(view.getTextArea)
    prover.setDocument(theory_view ,
                       if (dir.startsWith(Plugin.VFS_PREFIX)) dir.substring(Plugin.VFS_PREFIX.length) else dir)
    theory_view.activate
    prover.outputInfo.add( text => {
        output_text_view.append(text)
        val dockable = view.getDockableWindowManager.getDockable("isabelle-output")
        //link process output if dockable is active
        if(dockable != null) {
          val output_dockable = dockable.asInstanceOf[OutputDockable]
          if(output_dockable.getComponent(0) != output_text_view ) {
            output_dockable.asInstanceOf[OutputDockable].removeAll
            output_dockable.asInstanceOf[OutputDockable].add(new JScrollPane(output_text_view))
            output_dockable.revalidate
          }
        }
      })
    
    //register for state-view
    stateUpdate.add(state => {
      val state_view = view.getDockableWindowManager.getDockable("isabelle-state")
      val state_panel = if(state_view != null) state_view.asInstanceOf[StateViewDockable].panel else null
      if(state_panel != null){
        if (state == null)
          state_panel.setDocument(null : Document)
        else
          state_panel.setDocument(state.results_xml, UserAgent.baseURL)
      }
    })
 
    //register for theory-view

    // could also use this:
    // prover.commandInfo.add(c => Plugin.theory_view.repaint(c.command))

  }

  def deactivate {
    //TODO: clean up!
  }

}
