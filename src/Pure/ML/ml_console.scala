/*  Title:      Pure/ML/ml_console.scala
    Author:     Makarius

The raw ML process in interactive mode.
*/

package isabelle


import scala.collection.mutable


object ML_Console {
  /* command line entry point */

  def main(args: Array[String]): Unit = {
    Command_Line.tool {
      val dir_args = new mutable.ListBuffer[Path]
      val include_sessions = new mutable.ListBuffer[String]
      var logic = Isabelle_System.default_logic()
      var modes: List[String] = Nil
      var no_build = false
      var options = Options.init()
      var raw_ml_system = false

      val getopts = Getopts("""
Usage: isabelle console [OPTIONS]

  Options are:
    -d DIR       include session directory
    -i NAME      include session in name-space of theories
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(logic) + """)
    -m MODE      add print mode for output
    -n           no build of session image on startup
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -r           bootstrap from raw Poly/ML

  Build a logic session image and run the raw Isabelle ML process
  in interactive mode, with line editor ISABELLE_LINE_EDITOR=""" +
  quote(Isabelle_System.getenv("ISABELLE_LINE_EDITOR")) + """.
""",
        "d:" -> (arg => dir_args += Path.explode(arg)),
        "i:" -> (arg => include_sessions += arg),
        "l:" -> (arg => logic = arg),
        "m:" -> (arg => modes = arg :: modes),
        "n" -> (_ => no_build = true),
        "o:" -> (arg => options = options + arg),
        "r" -> (_ => raw_ml_system = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val dirs = dir_args.toList

      val store = Store(options)

      // build logic
      if (!no_build && !raw_ml_system) {
        val progress = new Console_Progress()
        val results =
          progress.interrupt_handler {
            Build.build_logic(options, logic, build_heap = true, progress = progress, dirs = dirs)
          }
        if (!results.ok) sys.exit(results.rc)
      }

      val session_background =
        if (raw_ml_system) {
          Sessions.Background(
            base = Sessions.Base.bootstrap,
            sessions_structure = Sessions.load_structure(options, dirs = dirs))
        }
        else {
          Sessions.background(
            options, logic, dirs = dirs, include_sessions = include_sessions.toList).check_errors
        }

      val session_heaps =
        if (raw_ml_system) Nil
        else store.session_heaps(session_background, logic = logic)

      // process loop
      val process =
        ML_Process(options, session_background, session_heaps, args = List("-i"), redirect = true,
          modes = if (raw_ml_system) Nil else modes ::: List("ASCII"))

      val rc =
        Exn.Interrupt.signal_handler { process.interrupt() } {
          new TTY_Loop(process.stdin, process.stdout).join()
          process.join()
        }
      if (rc != Process_Result.RC.ok) sys.exit(rc)
    }
  }
}
