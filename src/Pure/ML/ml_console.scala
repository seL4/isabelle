/*  Title:      Pure/ML/ml_console.scala
    Author:     Makarius

The raw ML process in interactive mode.
*/

package isabelle


object ML_Console
{
  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool {
      var dirs: List[Path] = Nil
      var logic = Isabelle_System.getenv("ISABELLE_LOGIC")
      var modes: List[String] = Nil
      var no_build = false
      var options = Options.init()
      var raw_ml_system = false
      var system_mode = false

      val getopts = Getopts("""
Usage: isabelle console [OPTIONS]

  Options are:
    -d DIR       include session directory
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(logic) + """)
    -m MODE      add print mode for output
    -n           no build of session image on startup
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -r           bootstrap from raw Poly/ML
    -s           system build mode for session image

  Build a logic session image and run the raw Isabelle ML process
  in interactive mode, with line editor ISABELLE_LINE_EDITOR=""" +
  quote(Isabelle_System.getenv("ISABELLE_LINE_EDITOR")) + """.
""",
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
        "l:" -> (arg => logic = arg),
        "m:" -> (arg => modes = arg :: modes),
        "n" -> (arg => no_build = true),
        "o:" -> (arg => options = options + arg),
        "r" -> (_ => raw_ml_system = true),
        "s" -> (_ => system_mode = true))

      val more_args = getopts(args)
      if (!more_args.isEmpty) getopts.usage()


      // build logic
      if (!no_build && !raw_ml_system) {
        val progress = new Console_Progress()
        val rc =
          progress.interrupt_handler {
            Build.build_logic(options, logic, build_heap = true, progress = progress,
              dirs = dirs, system_mode = system_mode)
          }
        if (rc != 0) sys.exit(rc)
      }

      // process loop
      val process =
        ML_Process(options, logic = logic, args = List("-i"), dirs = dirs, redirect = true,
          modes = if (raw_ml_system) Nil else modes ::: List("ASCII"),
          raw_ml_system = raw_ml_system,
          store = Some(Sessions.store(options, system_mode)),
          session_base =
            if (raw_ml_system) None
            else Some(Sessions.base_info(options, logic, dirs = dirs).check_base))

      val tty_loop = new TTY_Loop(process.stdin, process.stdout, Some(process.interrupt _))
      val process_result = Future.thread[Int]("process_result") {
        val rc = process.join
        tty_loop.cancel  // FIXME does not quite work, cannot interrupt blocking read on System.in
        rc
      }
      tty_loop.join
      process_result.join
    }
  }
}
