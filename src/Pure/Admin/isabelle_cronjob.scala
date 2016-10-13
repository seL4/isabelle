/*  Title:      Pure/Admin/isabelle_cronjob.scala
    Author:     Makarius

Main entry point for administrative cronjob at TUM.
*/

package isabelle


import scala.annotation.tailrec
import scala.collection.mutable


object Isabelle_Cronjob
{
  /* file-system state: owned by main cronjob */

  val main_dir = Path.explode("~/cronjob")
  val main_state_file = main_dir + Path.explode("run/main.state")
  val main_log = main_dir + Path.explode("log/main.log")  // owned by log service

  val isabelle_repos = main_dir + Path.explode("isabelle-build_history")
  val afp_repos = main_dir + Path.explode("AFP-build_history")



  /** particular tasks **/

  /* identify Isabelle + AFP repository snapshots */

  private def pull_repos(root: Path): String =
  {
    val hg = Mercurial.repository(root)
    hg.pull(options = "-q")
    hg.identify("tip", options = "-i")
  }

  private val isabelle_identify =
    Logger_Task("isabelle_identify", logger =>
      {
        val isabelle_id = pull_repos(isabelle_repos)
        val afp_id = pull_repos(afp_repos)

        val log_dir = main_dir + Build_Log.log_subdir(logger.start_date)
        Isabelle_System.mkdirs(log_dir)

        File.write(log_dir + Build_Log.log_filename("isabelle_identify", logger.start_date),
          terminate_lines(
            List("isabelle_identify: " + Build_Log.print_date(logger.start_date),
              "",
              "Isabelle version: " + isabelle_id,
              "AFP version: " + afp_id)))
      })


  /* integrity test of build_history vs. build_history_base */

  private val build_history_base =
    Logger_Task("build_history_base", logger =>
      {
        val log_dir = main_dir + Build_Log.log_subdir(logger.start_date)
        Isabelle_System.mkdirs(log_dir)

        for {
          (result, log_path) <-
            Build_History.build_history(Mercurial.repository(isabelle_repos),
              rev = "build_history_base", fresh = true, build_args = List("FOL"))
        } {
          result.check
          File.copy(log_path, log_dir + log_path.base)
        }
      })



  /** task logging **/

  sealed case class Logger_Task(name: String = "", body: Logger => Unit)

  class Log_Service private[Isabelle_Cronjob](progress: Progress)
  {
    private val thread: Consumer_Thread[String] =
      Consumer_Thread.fork("cronjob: logger", daemon = true)(
        consume = (text: String) =>
          {
            File.append(main_log, text + "\n")   // critical
            progress.echo(text)
            true
          })

    def shutdown() { thread.shutdown() }

    val hostname = Isabelle_System.hostname()

    def log(date: Date, task_name: String, msg: String): Unit =
      if (task_name != "")
        thread.send(
          "[" + Build_Log.print_date(date) + ", " + hostname + ", " + task_name + "]: " + msg)

    def start_logger(start_date: Date, task_name: String): Logger =
      new Logger(this, start_date, task_name)

    def run_task(start_date: Date, task: Logger_Task)
    {
      val logger = start_logger(start_date, task.name)
      val res = Exn.capture { task.body(logger) }
      val end_date = Date.now()
      val err =
        res match {
          case Exn.Res(_) => None
          case Exn.Exn(exn) => Some(Exn.message(exn))
        }
      logger.log_end(end_date, err)
    }

    def fork_task(start_date: Date, task: Logger_Task): Task =
      new Task(task.name, run_task(start_date, task))
  }

  class Logger private[Isabelle_Cronjob](
    val log_service: Log_Service, val start_date: Date, val task_name: String)
  {
    def log(date: Date, msg: String): Unit = log_service.log(date, task_name, msg)

    def log_end(end_date: Date, err: Option[String])
    {
      val elapsed_time = end_date.time - start_date.time
      val msg =
        (if (err.isEmpty) "finished" else "ERROR " + err.get) +
        (if (elapsed_time.seconds < 3.0) "" else ", elapsed time " + elapsed_time.message_hms)
      log(end_date, msg)
    }

    log(start_date, "started")
  }

  class Task private[Isabelle_Cronjob](name: String, body: => Unit)
  {
    private val future: Future[Unit] = Future.thread("cronjob: " + name) { body }
    def is_finished: Boolean = future.is_finished
  }



  /** cronjob **/

  def init_options(): Options = Options.load(Path.explode("~~/Admin/cronjob/cronjob.options"))

  def cronjob(progress: Progress, exclude_task: Set[String])
  {
    /* soft lock */

    val still_running =
      try { Some(File.read(main_state_file)) }
      catch { case ERROR(_) => None }

    still_running match {
      case None | Some("") =>
      case Some(running) =>
        error("Isabelle cronjob appears to be still running: " + running)
    }

    val main_start_date = Date.now()
    val log_service = new Log_Service(progress)

    File.write(main_state_file, main_start_date + " " + log_service.hostname)


    /* run tasks */

    def run(start_date: Date, task: Logger_Task): Unit =
      log_service.run_task(start_date, task)

    def run_sequential(tasks: Logger_Task*): Unit =
      for (task <- tasks.iterator if !exclude_task(task.name) || task.name == "")
        run(Date.now(), task)

    def run_parallel(tasks: Logger_Task*)
    {
      @tailrec def join(running: List[Task])
      {
        running.partition(_.is_finished) match {
          case (Nil, Nil) =>
          case (Nil, _ :: _) => Thread.sleep(500); join(running)
          case (_ :: _, remaining) => join(remaining)
        }
      }

      val start_date = Date.now()
      val running =
        for (task <- tasks.toList if !exclude_task(task.name))
          yield log_service.fork_task(start_date, task)
      join(running)
    }

    def SEQ(tasks: Logger_Task*): Logger_Task =
      Logger_Task(body = _ => run_sequential(tasks:_*))

    def PAR(tasks: Logger_Task*): Logger_Task =
      Logger_Task(body = _ => run_parallel(tasks:_*))


    /* main */

    run(main_start_date,
      Logger_Task("isabelle_cronjob", _ =>
        run_sequential(isabelle_identify, build_history_base)))

    log_service.shutdown()

    main_state_file.file.delete
  }



  /** command line entry point **/

  def main(args: Array[String])
  {
    Command_Line.tool0 {
      var force = false
      var verbose = false
      var exclude_task = Set.empty[String]

      val getopts = Getopts("""
Usage: Admin/cronjob/main [OPTIONS]

  Options are:
    -f           apply force to do anything
    -v           verbose
    -x NAME      exclude tasks with this name
""",
        "f" -> (_ => force = true),
        "v" -> (_ => verbose = true),
        "x:" -> (arg => exclude_task += arg))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = if (verbose) new Console_Progress() else Ignore_Progress

      if (force) cronjob(progress, exclude_task)
      else error("Need to apply force to do anything")
    }
  }
}
