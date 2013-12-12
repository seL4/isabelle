/*  Title:      Pure/Tools/simplifier_trace.scala
    Author:     Lars Hupel, TU Muenchen

Interactive Simplifier trace.
*/

package isabelle


object Simplifier_Trace
{
  /* PIDE protocol */

  class Handler extends Session.Protocol_Handler
  {
    val functions = Map.empty[String, (Session.Prover, Isabelle_Process.Protocol_Output) => Boolean]
  }
}
