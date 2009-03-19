/*
 * Independent prover sessions
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit


import isabelle.prover.{Prover, Command}
import isabelle.renderer.UserAgent

import org.w3c.dom.Document

import org.gjt.sp.jedit.{jEdit, EBMessage, EBPlugin, Buffer, EditPane, View}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.msg.{EditPaneUpdate, PropertiesChanged}

import javax.swing.{JTextArea, JScrollPane}


class ProverSetup(buffer: JEditBuffer)
{
  var prover: Prover = null
  var theory_view: TheoryView = null

  val state_update = new EventBus[Command]

  private var _selected_state: Command = null
  def selected_state = _selected_state
  def selected_state_=(state: Command) { _selected_state = state; state_update.event(state) }

  val output_text_view = new JTextArea

  def activate(view: View) {
    prover = new Prover(Isabelle.system, Isabelle.default_logic)
    prover.start() //start actor
    val buffer = view.getBuffer
    val path = buffer.getPath

    theory_view = new TheoryView(view.getTextArea, prover)
    prover.set_document(theory_view.change_receiver,
    if (path.startsWith(Isabelle.VFS_PREFIX)) path.substring(Isabelle.VFS_PREFIX.length) else path)
    theory_view.activate

    //register output-view
    prover.output_info += (text =>
      {
        output_text_view.append(text)
        val dockable = view.getDockableWindowManager.getDockable("isabelle-output")
        //link process output if dockable is active
        if (dockable != null) {
          val output_dockable = dockable.asInstanceOf[OutputDockable]
          if (output_dockable.getComponent(0) != output_text_view ) {
            output_dockable.asInstanceOf[OutputDockable].removeAll
            output_dockable.asInstanceOf[OutputDockable].add(new JScrollPane(output_text_view))
            output_dockable.revalidate
          }
        }
      })

    //register for state-view
    state_update += (state => {
      val state_view = view.getDockableWindowManager.getDockable("isabelle-state")
      val state_panel =
        if (state_view != null) state_view.asInstanceOf[StateViewDockable].panel
        else null
      if (state_panel != null) {
        if (state == null)
          state_panel.setDocument(null: Document)
        else
          state_panel.setDocument(state.result_document, UserAgent.baseURL)
      }
    })

  }

  def deactivate {
    buffer.setTokenMarker(buffer.getMode.getTokenMarker)
    theory_view.deactivate
    prover.stop
  }

}
