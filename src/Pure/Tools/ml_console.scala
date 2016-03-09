/*  Title:      Pure/Tools/ml_console.scala
    Author:     Makarius

Run Isabelle process with raw ML console and line editor.
*/

package isabelle


import java.io.{IOException, BufferedReader, InputStreamReader}


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
      var system_mode = false

      val getopts = Getopts("""
Usage: isabelle console [OPTIONS]

  Options are:
    -d DIR       include session directory
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(logic) + """)
    -m MODE      add print mode for output
    -n           no build of session image on startup
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -r           logic session is RAW_ML_SYSTEM
    -s           system build mode for session image

  Run Isabelle process with raw ML console and line editor
  (ISABELLE_LINE_EDITOR=""" + quote(Isabelle_System.getenv("ISABELLE_LINE_EDITOR")) + """.
""",
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
        "l:" -> (arg => logic = arg),
        "m:" -> (arg => modes = arg :: modes),
        "n" -> (arg => no_build = true),
        "o:" -> (arg => options = options + arg),
        "r" -> (_ => logic = "RAW_ML_SYSTEM"),
        "s" -> (_ => system_mode = true))

      val more_args = getopts(args)
      if (!more_args.isEmpty) getopts.usage()


      // build
      if (!no_build && logic != "RAW_ML_SYSTEM" &&
          Build.build(options = options, build_heap = true, no_build = true,
            dirs = dirs, system_mode = system_mode, sessions = List(logic)) != 0)
      {
        val progress = new Console_Progress
        progress.echo("Build started for Isabelle/" + logic + " ...")
        progress.interrupt_handler {
          val rc =
            Build.build(options = options, progress = progress, build_heap = true,
              dirs = dirs, system_mode = system_mode, sessions = List(logic))
          if (rc != 0) sys.exit(rc)
        }
      }

      // process loop
      val process =
        ML_Process(options, heap = logic, args = List("-i"),
          modes = if (logic == "RAW_ML_SYSTEM") Nil else modes ::: List("ASCII"))
      val process_output = Future.thread[Unit]("process_output") {
        try {
          var result = new StringBuilder(100)
          var finished = false
          while (!finished) {
            var c = -1
            var done = false
            while (!done && (result.length == 0 || process.stdout.ready)) {
              c = process.stdout.read
              if (c >= 0) result.append(c.asInstanceOf[Char])
              else done = true
            }
            if (result.length > 0) {
              System.out.print(result.toString)
              System.out.flush()
              result.length = 0
            }
            else {
              process.stdout.close()
              finished = true
            }
          }
        }
        catch { case e: IOException => case Exn.Interrupt() => }
      }
      val process_input = Future.thread[Unit]("process_input") {
        val reader = new BufferedReader(new InputStreamReader(System.in))
        POSIX_Interrupt.handler { process.interrupt } {
          try {
            var finished = false
            while (!finished) {
              reader.readLine() match {
                case null =>
                  process.stdin.close()
                  finished = true
                case line =>
                  process.stdin.write(line)
                  process.stdin.write("\n")
                  process.stdin.flush()
              }
            }
          }
          catch { case e: IOException => case Exn.Interrupt() => }
        }
      }
      val process_result = Future.thread[Int]("process_result") {
        val rc = process.join
        process_input.cancel
        rc
      }

      process_output.join
      process_input.join
      process_result.join
    }
  }
}
