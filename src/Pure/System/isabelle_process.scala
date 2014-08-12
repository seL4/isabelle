/*  Title:      Pure/System/isabelle_process.scala
    Author:     Makarius

Isabelle process wrapper.
*/

package isabelle


class Isabelle_Process(
  receiver: Prover.Message => Unit = Console.println(_),
  prover_args: List[String] = Nil) extends Prover(receiver,
    {
      val system_channel = System_Channel()
      try {
        val cmdline =
          Isabelle_System.getenv_strict("ISABELLE_PROCESS") ::
            (system_channel.prover_args ::: prover_args)
        val process =
          new Isabelle_System.Managed_Process(null, null, false, cmdline: _*) with
            Prover.System_Process { def channel = system_channel }
        process.stdin.close
        process
      }
      catch { case exn @ ERROR(_) => system_channel.accepted(); throw(exn) }
    })
{
  def encode(s: String): String = Symbol.encode(s)
  def decode(s: String): String = Symbol.decode(s)
}

