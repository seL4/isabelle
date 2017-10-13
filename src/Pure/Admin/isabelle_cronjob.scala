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

  val jenkins_jobs = "identify" :: Jenkins.build_log_jobs



  /** particular tasks **/

  /* identify Isabelle + AFP repository snapshots and build release */

  private val build_release =
    Logger_Task("build_release", logger =>
        {
          Isabelle_Devel.make_index()

          val rev = Mercurial.repository(isabelle_repos).id()
          val afp_rev = Mercurial.setup_repository(AFP.repos_source, afp_repos).id()

          File.write(logger.log_dir + Build_Log.log_filename("isabelle_identify", logger.start_date),
            Build_Log.Identify.content(logger.start_date, Some(rev), Some(afp_rev)))

          Isabelle_Devel.release_snapshot(rev = rev, afp_rev = afp_rev,
            parallel_jobs = 4, remote_mac = "macbroy31")
        })


  /* integrity test of build_history vs. build_history_base */

  private val build_history_base =
    Logger_Task("build_history_base", logger =>
      {
        val hg =
          Mercurial.setup_repository(
            File.standard_path(isabelle_repos), isabelle_repos_test)
        for {
          (result, log_path) <-
            Build_History.build_history(
              hg, rev = "build_history_base", fresh = true, build_args = List("HOL"))
        } {
          result.check
          File.move(log_path, logger.log_dir + log_path.base)
        }
      })


  /* remote build_history */

  sealed case class Item(known: Boolean, isabelle_version: String, pull_date: Date)
  {
    def unknown: Boolean = !known
  }

  def recent_items(db: SQL.Database, days: Int, rev: String, sql: SQL.Source): List[Item] =
  {
    val select =
      Build_Log.Data.select_recent_versions(days = days, rev = rev, sql = "WHERE " + sql)

    db.using_statement(select)(stmt =>
      stmt.execute_query().iterator(res =>
      {
        val known = res.bool(Build_Log.Data.known)
        val isabelle_version = res.string(Build_Log.Prop.isabelle_version)
        val pull_date = res.date(Build_Log.Data.pull_date)
        Item(known, isabelle_version, pull_date)
      }).toList)
  }

  def unknown_runs(items: List[Item]): List[List[Item]] =
  {
    val (run, rest) = Library.take_prefix[Item](_.unknown, items.dropWhile(_.known))
    if (run.nonEmpty) run :: unknown_runs(rest) else Nil
  }

  sealed case class Remote_Build(
    description: String,
    host: String,
    user: String = "",
    port: Int = 0,
    shared_home: Boolean = true,
    historic: Boolean = false,
    history: Int = 0,
    history_base: String = "build_history_base",
    options: String = "",
    args: String = "",
    detect: SQL.Source = "")
  {
    def sql: SQL.Source =
      Build_Log.Prop.build_engine + " = " + SQL.string(Build_History.engine) + " AND " +
      Build_Log.Prop.build_host + " = " + SQL.string(host) +
      (if (detect == "") "" else " AND " + SQL.enclose(detect))

    def profile: Build_Status.Profile =
      Build_Status.Profile(description, history, sql)

    def history_base_filter(hg: Mercurial.Repository): Set[String] =
    {
      val rev0 = hg.id(history_base)
      val graph = hg.graph()
      (rev0 :: graph.all_succs(List(rev0))).toSet
    }

    def pick(options: Options, rev: String = "", filter: String => Boolean = (_: String) => true)
      : Option[String] =
    {
      val store = Build_Log.store(options)
      using(store.open_database())(db =>
      {
        def pick_days(days: Int, gap: Int): Option[String] =
        {
          val items =
            recent_items(db, days = days, rev = rev, sql = sql).
              filter(item => filter(item.isabelle_version))
          def runs = unknown_runs(items).filter(run => run.length >= gap)

          val known_rev =
            rev != "" && items.exists(item => item.known && item.isabelle_version == rev)

          if (historic || known_rev) {
            val longest_run =
              (List.empty[Item] /: runs)({ case (item1, item2) =>
                if (item1.length >= item2.length) item1 else item2
              })
            if (longest_run.isEmpty) None
            else Some(longest_run(longest_run.length / 2).isabelle_version)
          }
          else if (rev != "") Some(rev)
          else runs.flatten.headOption.map(_.isabelle_version)
        }

        pick_days(options.int("build_log_history") max history, 2) orElse
        pick_days(200, 5) orElse
        pick_days(2000, 1)
      })
    }
  }

  val remote_builds_old: List[Remote_Build] =
    List(
      Remote_Build("Poly/ML 5.7 Linux", "lxbroy8",
        history_base = "37074e22e8be",
        options = "-m32 -B -M1x2,2 -t polyml-5.7 -i 'init_component /home/isabelle/contrib/polyml-5.7'",
        args = "-N -g timing",
        detect = Build_Log.Prop.build_tags + " = " + SQL.string("polyml-5.7") + " AND " +
          Build_Log.Settings.ML_OPTIONS + " <> " + SQL.string("-H 500")),
      Remote_Build("Poly/ML 5.7 Mac OS X", "macbroy2",
        history_base = "37074e22e8be",
        options = "-m32 -B -M1x4,4 -t polyml-5.7 -i 'init_component /home/isabelle/contrib/polyml-5.7'",
        args = "-a",
        detect = Build_Log.Prop.build_tags + " = " + SQL.string("polyml-5.7")),
      Remote_Build("Poly/ML test", "lxbroy8",
        options = "-m32 -B -M1x2,2 -t polyml-test -i 'init_component /home/isabelle/contrib/polyml-5.7-20170217'",
        args = "-N -g timing",
        detect = Build_Log.Prop.build_tags + " = " + SQL.string("polyml-test")),
      Remote_Build("Mac OS X 10.8 Mountain Lion", "macbroy30", options = "-m32 -M2", args = "-a",
        detect = Build_Log.Prop.build_start + " < date '2017-03-03'"))


  val remote_builds: List[List[Remote_Build]] =
  {
    List(
      List(Remote_Build("Poly/ML 5.7.1 Linux", "lxbroy8",
        history_base = "37074e22e8be",
        options = "-m32 -B -M1x2,2 -t polyml-5.7.1-pre1 -i 'init_component /home/isabelle/contrib/polyml-test-e7a662f8f9c4'",
        args = "-N -g timing",
        detect = Build_Log.Prop.build_tags + " = " + SQL.string("polyml-5.7.1-pre1"))),
      List(Remote_Build("Linux A", "lxbroy9",
        options = "-m32 -B -M1x2,2", args = "-N -g timing")),
      List(Remote_Build("Linux B", "lxbroy10", historic = true, history = 90,
        options = "-m32 -B -M1x4,2,4,6", args = "-N -g timing")),
      List(
        Remote_Build("Mac OS X 10.9 Mavericks", "macbroy2",
          options = "-m32 -M8" +
            " -e ISABELLE_GHC=ghc -e ISABELLE_MLTON=mlton -e ISABELLE_OCAML=ocaml" +
            " -e ISABELLE_OCAMLC=ocamlc -e ISABELLE_SMLNJ=/mnt/nfsbroy/home/smlnj/bin/sml",
          args = "-a",
          detect = Build_Log.Prop.build_tags.undefined),
        Remote_Build("Mac OS X 10.9 Mavericks, quick_and_dirty", "macbroy2",
          options = "-m32 -M8 -t quick_and_dirty", args = "-a -o quick_and_dirty",
          detect = Build_Log.Prop.build_tags + " = " + SQL.string("quick_and_dirty")),
        Remote_Build("Mac OS X 10.9 Mavericks, skip_proofs", "macbroy2",
          options = "-m32 -M8 -t skip_proofs", args = "-a -o skip_proofs",
          detect = Build_Log.Prop.build_tags + " = " + SQL.string("skip_proofs")),
        Remote_Build("Poly/ML 5.7.1 Mac OS X", "macbroy2",
          history_base = "37074e22e8be",
          options = "-m32 -B -M1x4,4 -t polyml-5.7.1-pre1 -i 'init_component /home/isabelle/contrib/polyml-test-e7a662f8f9c4'",
          args = "-a",
          detect = Build_Log.Prop.build_tags + " = " + SQL.string("polyml-5.7.1-pre1"))),
      List(
        Remote_Build("Mac OS X 10.12 Sierra", "macbroy30", options = "-m32 -M2", args = "-a",
          detect = Build_Log.Prop.build_start + " > date '2017-03-03'")),
      List(Remote_Build("Mac OS X 10.10 Yosemite", "macbroy31", options = "-m32 -M2", args = "-a")),
      List(
        Remote_Build("Windows", "vmnipkow9", historic = true, history = 90, shared_home = false,
          options = "-m32 -M4" +
            " -e ISABELLE_OCAML=ocaml -e ISABELLE_OCAMLC=ocamlc" +
            " -e ISABELLE_GHC=/usr/local/ghc-8.0.2/bin/ghc" +
            " -e ISABELLE_SMLNJ=/usr/local/smlnj-110.81/bin/sml",
          args = "-a",
          detect = Build_Log.Settings.ML_PLATFORM + " = " + SQL.string("x86-windows")),
        Remote_Build("Windows", "vmnipkow9", historic = true, history = 90, shared_home = false,
          options = "-m64 -M4" +
            " -e ISABELLE_OCAML=ocaml -e ISABELLE_OCAMLC=ocamlc" +
            " -e ISABELLE_GHC=/usr/local/ghc-8.0.2/bin/ghc" +
            " -e ISABELLE_SMLNJ=/usr/local/smlnj-110.81/bin/sml",
          args = "-a",
          detect = Build_Log.Settings.ML_PLATFORM + " = " + SQL.string("x86_64-windows"))))
  }

  private def remote_build_history(rev: String, i: Int, r: Remote_Build): Logger_Task =
  {
    val task_name = "build_history-" + r.host
    Logger_Task(task_name, logger =>
      {
        using(logger.ssh_context.open_session(host = r.host, user = r.user, port = r.port))(
          ssh =>
            {
              val self_update = !r.shared_home
              val push_isabelle_home = self_update && Mercurial.is_repository(Path.explode("~~"))

              val results =
                Build_History.remote_build_history(ssh,
                  isabelle_repos,
                  isabelle_repos.ext(r.host),
                  isabelle_identifier = "cronjob_build_history",
                  self_update = self_update,
                  push_isabelle_home = push_isabelle_home,
                  rev = rev,
                  options =
                    " -N " + Bash.string(task_name) + (if (i < 0) "" else "_" + (i + 1).toString) +
                    " -f " + r.options,
                  args = "-o timeout=10800 " + r.args)

              for ((log_name, bytes) <- results) {
                logger.log(Date.now(), log_name)
                Bytes.write(logger.log_dir + Path.explode(log_name), bytes)
              }
            })
      })
  }

  val build_status_profiles: List[Build_Status.Profile] =
    (remote_builds_old :: remote_builds).flatten.map(_.profile)



  /** task logging **/

  sealed case class Logger_Task(name: String = "", body: Logger => Unit)

  class Log_Service private[Isabelle_Cronjob](progress: Progress, val ssh_context: SSH.Context)
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
          case Exn.Exn(exn) =>
            System.err.println("Exception trace for " + quote(task.name) + ":")
            exn.printStackTrace()
            val first_line = Library.split_lines(Exn.message(exn)).headOption getOrElse "exception"
            Some(first_line)
        }
      logger.log_end(end_date, err)
    }

    def fork_task(start_date: Date, task: Logger_Task): Task =
      new Task(task.name, run_task(start_date, task))
  }

  class Logger private[Isabelle_Cronjob](
    val log_service: Log_Service, val start_date: Date, val task_name: String)
  {
    def ssh_context: SSH.Context = log_service.ssh_context
    def options: Options = ssh_context.options

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

    val log_service = new Log_Service(progress, SSH.init_context(Options.init()))

    def run(start_date: Date, task: Logger_Task) { log_service.run_task(start_date, task) }

    def run_now(task: Logger_Task) { run(Date.now(), task) }


    /* structured tasks */

    def SEQ(tasks: List[Logger_Task]): Logger_Task = Logger_Task(body = _ =>
      for (task <- tasks.iterator if !exclude_task(task.name) || task.name == "")
        run_now(task))

    def PAR(tasks: List[Logger_Task]): Logger_Task = Logger_Task(body = _ =>
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
          for (task <- tasks if !exclude_task(task.name))
            yield log_service.fork_task(start_date, task)
        join(running)
      })


    /* main */

    val main_start_date = Date.now()
    File.write(main_state_file, main_start_date + " " + log_service.hostname)

    val hg = Mercurial.repository(isabelle_repos)
    val rev = hg.id()

    run(main_start_date,
      Logger_Task("isabelle_cronjob", logger =>
        run_now(
          SEQ(List(build_release, build_history_base,
            PAR(remote_builds.map(seq =>
              SEQ(
                for {
                  (r, i) <- (if (seq.length <= 1) seq.map((_, -1)) else seq.zipWithIndex)
                  rev <- r.pick(logger.options, rev, r.history_base_filter(hg))
                } yield remote_build_history(rev, i, r)))),
            Logger_Task("jenkins_logs", _ => Jenkins.download_logs(jenkins_jobs, main_dir)),
            Logger_Task("build_log_database",
              logger => Isabelle_Devel.build_log_database(logger.options)),
            Logger_Task("build_status",
              logger => Isabelle_Devel.build_status(logger.options)))))))

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

      val progress = if (verbose) new Console_Progress() else No_Progress

      if (force) cronjob(progress, exclude_task)
      else error("Need to apply force to do anything")
    }
  }
}
