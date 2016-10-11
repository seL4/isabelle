/*  Title:      Pure/Admin/isabelle_cronjob.scala
    Author:     Makarius

Main entry point for administrative cronjob at TUM.
*/

package isabelle


object Isabelle_Cronjob
{
  /** file-system state: owned by main cronjob **/

  val main_dir = Path.explode("~/cronjob")
  val run_dir = main_dir + Path.explode("run")
  val log_dir = main_dir + Path.explode("log")

  val main_state_file = run_dir + Path.explode("main.state")
  val main_log = log_dir + Path.explode("main.log")


  /* managed repository clones */

  val isabelle_repos = main_dir + Path.explode("isabelle-build_history")
  val afp_repos = main_dir + Path.explode("AFP-build_history")

  def pull_repos(root: Path): String =
    using(Mercurial.open_repository(root))(hg =>
      {
        hg.pull(options = "-q")
        hg.identify("tip")
      })


  /** cronjob **/

  def cronjob(progress: Progress)
  {
    /* log */

    val hostname = Isabelle_System.hostname()

    def log(date: Date, msg: String)
    {
      val text = "[" + Build_Log.print_date(date) + " " + hostname + "]: " + msg
      File.append(main_log, text + "\n")
      progress.echo(text)
    }


    /* start */

    val start_date = Date.now()

    val still_running =
      try { Some(File.read(main_state_file)) }
      catch { case ERROR(_) => None }

    still_running match {
      case Some(running) =>
        error("Isabelle cronjob appears to be still running: " + running)
      case None =>
        File.write(main_state_file, start_date + " " + hostname)
        log(start_date, "start cronjob")
    }


    /* identify repository snapshots */

    {
      val pull_date = Date.now()

      val isabelle_id = pull_repos(isabelle_repos)
      val afp_id = pull_repos(afp_repos)

      val log_path = log_dir + Build_Log.log_path("isabelle_identify", pull_date)
      Isabelle_System.mkdirs(log_path.dir)
      File.write(log_path,
        Library.terminate_lines(
          List("isabelle_identify: " + Build_Log.print_date(pull_date),
            "",
            "Isabelle version: " + isabelle_id,
            "AFP version: " + afp_id)))
    }


    /* end */

    val end_date = Date.now()
    val elapsed_time = end_date.time - start_date.time

    log(end_date, "end cronjob, elapsed time " + elapsed_time.message_hms)

    main_state_file.file.delete
  }



  /** command line entry point **/

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

      val progress = if (verbose) new Console_Progress() else Ignore_Progress

      if (force) cronjob(progress)
      else error("Need to apply force to do anything")
    }
  }
}
