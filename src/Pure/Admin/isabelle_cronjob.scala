/*  Title:      Pure/Admin/isabelle_cronjob.scala
    Author:     Makarius

Main entry point for administrative cronjob at TUM.
*/

package isabelle


import scala.annotation.tailrec
import scala.collection.mutable


object Isabelle_Cronjob
{
  /** file-system state: owned by main cronjob **/

  val main_dir = Path.explode("~/cronjob")
  val run_dir = main_dir + Path.explode("run")
  val log_dir = main_dir + Path.explode("log")

  val main_state_file = run_dir + Path.explode("main.state")
  val main_log = log_dir + Path.explode("main.log")  // owned by logger


  /* managed repository clones */

  val isabelle_repos = main_dir + Path.explode("isabelle-build_history")
  val afp_repos = main_dir + Path.explode("AFP-build_history")

  def pull_repos(root: Path): String =
  {
    val hg = Mercurial.repository(root)
    hg.pull(options = "-q")
    hg.identify("tip", options = "-i")
  }



  /** particular tasks **/

  /* identify repository snapshots */

  def isabelle_identify(start_date: Date)
  {
    val isabelle_id = pull_repos(isabelle_repos)
    val afp_id = pull_repos(afp_repos)

    val log_path = log_dir + Build_Log.log_path("isabelle_identify", start_date)
    Isabelle_System.mkdirs(log_path.dir)
    File.write(log_path,
      Library.terminate_lines(
        List("isabelle_identify: " + Build_Log.print_date(start_date),
          "",
          "Isabelle version: " + isabelle_id,
          "AFP version: " + afp_id)))
  }



  /** cronjob **/

  private class Task(val name: String, body: Date => Unit)
  {
    override def toString: String = "cronjob: " + name

    val start_date: Date = Date.now()

    private val future: Future[Unit] = Future.thread(toString) { body(start_date) }
    def is_finished: Boolean = future.is_finished

    def success: Boolean =
      future.join_result match {
        case Exn.Res(_) => true
        case Exn.Exn(_) => false
      }
  }

  def cronjob(progress: Progress)
  {
    /* check */

    val still_running =
      try { Some(File.read(main_state_file)) }
      catch { case ERROR(_) => None }

    still_running match {
      case None | Some("") =>
      case Some(running) =>
        error("Isabelle cronjob appears to be still running: " + running)
    }


    /* logger */

    val hostname = Isabelle_System.hostname()

    val logger: Consumer_Thread[String] =
      Consumer_Thread.fork("cronjob: logger", daemon = true)(
        consume = (text: String) =>
          {
            File.append(main_log, text + "\n")
            progress.echo(text)
            true
          })

    def log(date: Date, task_name: String, msg: String)
    {
      logger.send(
        "[" + Build_Log.print_date(date) + ", " + hostname + ", " + task_name + "]: " + msg)
    }

    def log_start(task: Task) { log(task.start_date, task.name, "started") }

    def log_end(end_date: Date, task: Task)
    {
      val elapsed_time = end_date.time - task.start_date.time
      val msg =
        (if (task.success) "finished" else "FAILED") +
        (if (elapsed_time.seconds < 3.0) "" else ", elapsed time " + elapsed_time.message_hms)
      log(end_date, task.name, msg)
    }


    /* manage tasks */

    def manage_tasks(task_specs: List[(String, Date => Unit)])
    {
      @tailrec def await(running: List[Task])
      {
        running.partition(_.is_finished) match {
          case (Nil, Nil) =>
          case (Nil, _ :: _) => Thread.sleep(500); await(running)
          case (finished, remaining) =>
            val end_date = Date.now()
            finished.foreach(log_end(end_date, _))
            await(remaining)
        }
      }
      await(task_specs.map({ case (name, body) => new Task(name, body) }))
    }


    /* main */

    val main_task = new Task("main", _ => ())
    File.write(main_state_file, main_task.start_date + " " + hostname)
    log_start(main_task)

    manage_tasks(List("isabelle_identify" -> isabelle_identify _))

    log_end(Date.now(), main_task)
    main_state_file.file.delete

    logger.shutdown()
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
