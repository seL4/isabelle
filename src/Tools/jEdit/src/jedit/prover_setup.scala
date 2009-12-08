/*
 * Independent prover sessions for each buffer
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit


import org.gjt.sp.jedit.{Buffer, View}

import isabelle.proofdocument.{Prover, Theory_View}


class Prover_Setup(buffer: Buffer)
{
  var prover: Prover = null
  var theory_view: Theory_View = null

  def activate(view: View)
  {
    // Theory_View starts prover
    theory_view = new Theory_View(view.getTextArea)
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
