/*  Title:      Pure/System/isabelle_process.scala
    Author:     Makarius

Isabelle process wrapper.
*/

package isabelle


object Isabelle_Process
{
  def apply(
    options: Options,
    heap: String = "",
    args: List[String] = Nil,
    modes: List[String] = Nil,
    secure: Boolean = false,
    receiver: Prover.Receiver = Console.println(_)): Isabelle_Process =
  {
    val channel = System_Channel()
    val process =
      try {
        ML_Process(options, heap = heap, args = args, modes = modes, secure = secure,
          process_socket = channel.server_name)
      }
      catch { case exn @ ERROR(_) => channel.accepted(); throw exn }
    process.stdin.close

    new Isabelle_Process(receiver, channel, process)
  }


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool {
      var eval_args: List[String] = Nil
      var modes: List[String] = Nil
      var options = Options.init()

      val getopts = Getopts("""
Usage: isabelle_process [OPTIONS] [HEAP]

  Options are:
    -e ML_EXPR   evaluate ML expression on startup
    -f ML_FILE   evaluate ML file on startup
    -m MODE      add print mode for output
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  If HEAP is a plain name (default $ISABELLE_LOGIC), it is searched in
  $ISABELLE_PATH; if it contains a slash, it is taken as literal file;
  if it is RAW_ML_SYSTEM, the initial ML heap is used.
""",
        "e:" -> (arg => eval_args = eval_args ::: List("--eval", arg)),
        "f:" -> (arg => eval_args = eval_args ::: List("--use", arg)),
        "m:" -> (arg => modes = arg :: modes),
        "o:" -> (arg => options = options + arg))

      val heap =
        getopts(args) match {
          case Nil => ""
          case List(heap) => heap
          case _ => getopts.usage()
        }

      ML_Process(options, heap = heap, args = eval_args ::: args.toList, modes = modes).
        result().print_stdout.rc
    }
  }
}

class Isabelle_Process private(
    receiver: Prover.Receiver, channel: System_Channel, process: Prover.System_Process)
  extends Prover(receiver, channel, process)
{
  def encode(s: String): String = Symbol.encode(s)
  def decode(s: String): String = Symbol.decode(s)
}
