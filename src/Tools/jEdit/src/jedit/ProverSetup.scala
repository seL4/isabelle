/*
 * Independent prover sessions for each buffer
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit


import org.gjt.sp.jedit.{Buffer, View}

import isabelle.prover.Prover


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
    prover.begin_document(buffer.getName)
  }

  def deactivate()
  {
    theory_view.deactivate
    prover.stop
  }
}
