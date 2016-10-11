/*  Title:      Pure/Admin/isabelle_cronjob.scala
    Author:     Makarius

Main entry point for administrative cronjob at TUM.
*/

package isabelle


object Isabelle_Cronjob
{
  def main(args: Array[String])
  {
    Command_Line.tool0 {
      var force = false
      var verbose = false

      val getopts = Getopts("""
Usage: Admin/cronjob/main [OPTIONS]

  Options are:
    -f           apply force to do anything
    -v           verbose
""",
        "f" -> (_ => force = true),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      if (verbose) Output.writeln("This is the Isabelle cronjob")

      val rc =
        if (force) {
          Thread.sleep(Time.seconds(30).ms)
          0
        }
        else { Output.warning("Need to apply force to do anything"); 1 }

      if (rc != 0) sys.exit(rc)
    }
  }
}
