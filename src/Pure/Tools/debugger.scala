/*  Title:      Pure/Tools/debugger.scala
    Author:     Makarius

Interactive debugger for Isabelle/ML.
*/

package isabelle


object Debugger
{
  /* GUI interaction */

  case object Event


  /* manager thread */

  private lazy val manager: Consumer_Thread[Any] =
    Consumer_Thread.fork[Any]("Debugger.manager", daemon = true)(
      consume = (arg: Any) =>
      {
        // FIXME
        true
      },
      finish = () =>
      {
        // FIXME
      }
    )


  /* protocol handler */

  class Handler extends Session.Protocol_Handler
  {
    override def stop(prover: Prover)
    {
      manager.shutdown()
    }

    val functions = Map.empty[String, (Prover, Prover.Protocol_Output) => Boolean]  // FIXME
  }
}
