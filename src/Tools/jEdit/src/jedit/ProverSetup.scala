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


class ProverSetup(buffer: Buffer)
{
  var prover: Prover = null
  var theory_view: TheoryView = null


  def activate(view: View)
  {
    // TheoryView starts prover
    theory_view = new TheoryView(view.getTextArea)
    prover = theory_view.prover

    theory_view.activate()
    prover.set_document(buffer.getName)

  }

  def deactivate
  {
    theory_view.deactivate
    prover.stop
  }

}
