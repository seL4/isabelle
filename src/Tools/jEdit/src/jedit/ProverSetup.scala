/*
 * Independent prover sessions for each buffer
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

  val output_text_view = new JTextArea

  def activate(view: View)
  {
    prover = new Prover(Isabelle.system, Isabelle.default_logic)
    prover.start() // start actor
    val buffer = view.getBuffer

    theory_view = new TheoryView(view.getTextArea, prover)
    prover.set_document(theory_view.change_receiver, buffer.getName)

    // register output-view
    prover.output_info += (text =>
      {
        output_text_view.append(text + "\n")
        val dockable = view.getDockableWindowManager.getDockable("isabelle-output")
        // link process output if dockable is active
        if (dockable != null) {
          val output_dockable = dockable.asInstanceOf[OutputDockable]
          if (output_dockable.getComponent(0) != output_text_view ) {
            output_dockable.asInstanceOf[OutputDockable].removeAll
            output_dockable.asInstanceOf[OutputDockable].add(new JScrollPane(output_text_view))
            output_dockable.revalidate
          }
        }
      })

  }

  def deactivate
  {
    theory_view.deactivate
    prover.stop
  }

}
