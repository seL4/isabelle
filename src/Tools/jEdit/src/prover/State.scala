/*
 * Accumulating results from prover
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.prover

abstract class State
{
  def +(message: XML.Tree): State
}
