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
  val current_log = main_dir + Path.explode("run/main.log")  // owned by log service
  val cumulative_log = main_dir + Path.explode("log/main.log")  // owned by log service

  val isabelle_repos = main_dir + Path.explode("isabelle")
  val isabelle_repos_test = main_dir + Path.explode("isabelle-test")
  val afp_repos = main_dir + Path.explode("AFP")

  val release_snapshot = Path.explode("~/html-data/release_snapshot")



  /** particular tasks **/

  /* identify Isabelle + AFP repository snapshots */

  private val isabelle_identify =
    Logger_Task("isabelle_identify", logger =>
      {
        val isabelle_id = Mercurial.repository(isabelle_repos).id()
        val afp_id =
        {
          val hg = Mercurial.setup_repository(logger.cronjob_options.string("afp_repos"), afp_repos)
          hg.pull()
          hg.id()
        }

        File.write(logger.log_dir + Build_Log.log_filename("isabelle_identify", logger.start_date),
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
        for {
          (result, log_path) <-
            Build_History.build_history(Mercurial.repository(isabelle_repos_test),
              rev = "build_history_base", fresh = true, build_args = List("HOL"))
        } {
          result.check
          File.copy(log_path, logger.log_dir + log_path.base)
        }
      })


  /* build release from repository snapshot */

  private val build_release =
    Logger_Task("build_release", logger =>
      Isabelle_System.with_tmp_dir("isadist")(base_dir =>
        {
          val new_snapshot = release_snapshot.ext("new")
          val old_snapshot = release_snapshot.ext("old")

          Isabelle_System.rm_tree(new_snapshot)
          Isabelle_System.rm_tree(old_snapshot)

          Build_Release.build_release(base_dir, parallel_jobs = 4,
            remote_mac = "macbroy30", website = Some(new_snapshot))

          if (release_snapshot.is_dir) File.mv(release_snapshot, old_snapshot)
          File.mv(new_snapshot, release_snapshot)
          Isabelle_System.rm_tree(old_snapshot)
        }))


  /* remote build_history */

  private sealed case class Remote_Build(
    host: String,
    user: String = "",
    port: Int = SSH.default_port,
    shared_home: Boolean = false,
    options: String = "",
    args: String = "-a")

  private val remote_builds =
    List(
      Remote_Build("lxbroy10", options = "-m32 -M4", shared_home = true),
      Remote_Build("macbroy2", options = "-m32 -M4"))

  private def remote_build_history(rev: String, r: Remote_Build): Logger_Task =
    Logger_Task("build_history-" + r.host, logger =>
      {
        using(logger.ssh_context.open_session(host = r.host, user = r.user, port = r.port))(
          session =>
            {
              val results =
                Build_History.remote_build_history(session,
                  isabelle_repos,
                  isabelle_repos.ext(r.host),
                  isabelle_repos_source = logger.cronjob_options.string("isabelle_repos"),
                  self_update = !r.shared_home,
                  options = r.options + " -f -r " + File.bash_string(rev),
                  args = r.args)
              for ((log, bytes) <- results)
                Bytes.write(logger.log_dir + Path.explode(log), bytes)
            })
      })



  /** task logging **/

  sealed case class Logger_Task(name: String = "", body: Logger => Unit)

  class Log_Service private[Isabelle_Cronjob](
    progress: Progress, val cronjob_options: Options, val ssh_context: SSH)
  {
    current_log.file.delete

    private val thread: Consumer_Thread[String] =
      Consumer_Thread.fork("cronjob: logger", daemon = true)(
        consume = (text: String) =>
          { // critical
            File.append(current_log, text + "\n")
            File.append(cumulative_log, text + "\n")
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
    def cronjob_options: Options = log_service.cronjob_options
    def ssh_context: SSH = log_service.ssh_context

    def log(date: Date, msg: String): Unit = log_service.log(date, task_name, msg)

    def log_end(end_date: Date, err: Option[String])
    {
      val elapsed_time = end_date.time - start_date.time
      val msg =
        (if (err.isEmpty) "finished" else "ERROR " + err.get) +
        (if (elapsed_time.seconds < 3.0) "" else " (" + elapsed_time.message_hms + " elapsed time)")
      log(end_date, msg)
    }

    val log_dir: Path = main_dir + Build_Log.log_subdir(start_date)

    Isabelle_System.mkdirs(log_dir)
    log(start_date, "started")
  }

  class Task private[Isabelle_Cronjob](name: String, body: => Unit)
  {
    private val future: Future[Unit] = Future.thread("cronjob: " + name) { body }
    def is_finished: Boolean = future.is_finished
  }



  /** cronjob **/

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


    /* log service */

    val cronjob_options = Options.load(Path.explode("~~/Admin/cronjob/cronjob.options"))
    val ssh_context = SSH.init(Options.init())
    val log_service = new Log_Service(progress, cronjob_options, ssh_context)

    def run(start_date: Date, task: Logger_Task) { log_service.run_task(start_date, task) }

    def run_now(task: Logger_Task) { run(Date.now(), task) }


    /* structured tasks */

    def SEQ(tasks: Logger_Task*): Logger_Task = Logger_Task(body = _ =>
      for (task <- tasks.iterator if !exclude_task(task.name) || task.name == "")
        run_now(task))

    def PAR(tasks: Logger_Task*): Logger_Task = Logger_Task(body = _ =>
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
      })


    /* main */

    val main_start_date = Date.now()
    File.write(main_state_file, main_start_date + " " + log_service.hostname)

    val rev = Mercurial.repository(isabelle_repos).id()

    run(main_start_date,
      Logger_Task("isabelle_cronjob", _ =>
        run_now(
          SEQ(isabelle_identify, build_history_base, build_release,
            PAR(remote_builds.map(remote_build_history(rev, _)):_*)))))

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
