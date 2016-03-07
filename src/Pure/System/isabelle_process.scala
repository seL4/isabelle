/*  Title:      Pure/System/isabelle_process.scala
    Author:     Makarius

Isabelle process wrapper.
*/

package isabelle


object Isabelle_Process
{
  def apply(
    receiver: Prover.Message => Unit = Console.println(_),
    prover_args: List[String] = Nil): Isabelle_Process =
  {
    val system_channel = System_Channel()
    val system_process =
      try {
        val process =
          Bash.process("\"$ISABELLE_PROCESS\" -P " + File.bash_string(system_channel.server_name) +
            " " + File.bash_args(prover_args))
        process.stdin.close
        process
      }
      catch { case exn @ ERROR(_) => system_channel.accepted(); throw exn }

    new Isabelle_Process(receiver, system_channel, system_process)
  }


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool {
      var secure = false
      var ml_args: List[String] = Nil
      var modes: List[String] = Nil
      var options = Options.init()

      val getopts = Getopts("""
Usage: isabelle_process [OPTIONS] [HEAP]

  Options are:
    -S           secure mode -- disallow critical operations
    -e ML_EXPR   evaluate ML expression on startup
    -f ML_FILE   evaluate ML file on startup
    -m MODE      add print mode for output
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  If HEAP is a plain name (default $ISABELLE_LOGIC), it is searched in
  $ISABELLE_PATH; if it contains a slash, it is taken as literal file;
  if it is RAW_ML_SYSTEM, the initial ML heap is used.
""",
        "S" -> (_ => secure = true),
        "e:" -> (arg => ml_args = ml_args ::: List("--eval", arg)),
        "f:" -> (arg => ml_args = ml_args ::: List("--use", arg)),
        "m:" -> (arg => modes = arg :: modes),
        "o:" -> (arg => options = options + arg))

      val heap =
        getopts(args) match {
          case Nil => ""
          case List(heap) => heap
          case _ => getopts.usage()
        }

      ML_Process(options, heap = heap, args = ml_args, secure = secure, modes = modes).
        result().print_stdout.rc
    }
  }
}

class Isabelle_Process private(
    receiver: Prover.Message => Unit,
    system_channel: System_Channel,
    system_process: Prover.System_Process)
  extends Prover(receiver, system_channel, system_process)
{
  def encode(s: String): String = Symbol.encode(s)
  def decode(s: String): String = Symbol.decode(s)
}
