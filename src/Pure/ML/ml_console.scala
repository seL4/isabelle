/*  Title:      Pure/ML/ml_console.scala
    Author:     Makarius

The raw ML process in interactive mode.
*/

package isabelle


object ML_Console
{
  /* command line entry point */

  def main(args: Array[String]): Unit =
  {
    Command_Line.tool {
      var dirs: List[Path] = Nil
      var include_sessions: List[String] = Nil
      var logic = Isabelle_System.getenv("ISABELLE_LOGIC")
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
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
        "i:" -> (arg => include_sessions = include_sessions ::: List(arg)),
        "l:" -> (arg => logic = arg),
        "m:" -> (arg => modes = arg :: modes),
        "n" -> (_ => no_build = true),
        "o:" -> (arg => options = options + arg),
        "r" -> (_ => raw_ml_system = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()


      val sessions_structure = Sessions.load_structure(options, dirs = dirs)
      val store = Sessions.store(options)

      // build logic
      if (!no_build && !raw_ml_system) {
        val progress = new Console_Progress()
        val rc =
          progress.interrupt_handler {
            Build.build_logic(options, logic, build_heap = true, progress = progress, dirs = dirs)
          }
        if (rc != 0) sys.exit(rc)
      }

      // process loop
      val process =
        ML_Process(options, sessions_structure, store,
          logic = logic, args = List("-i"), redirect = true,
          modes = if (raw_ml_system) Nil else modes ::: List("ASCII"),
          raw_ml_system = raw_ml_system,
          session_base =
            if (raw_ml_system) None
            else Some(Sessions.base_info(
              options, logic, dirs = dirs, include_sessions = include_sessions).check.base))

      POSIX_Interrupt.handler { process.interrupt() } {
        new TTY_Loop(process.stdin, process.stdout).join
        val rc = process.join
        if (rc != 0) sys.exit(rc)
      }
    }
  }
}
