/*  Title:      Pure/Admin/isabelle_cronjob.scala
    Author:     Makarius

Main entry point for administrative cronjob at TUM.
*/

package isabelle


import java.nio.file.Files

import scala.annotation.tailrec


object Isabelle_Cronjob {
  /* global resources: owned by main cronjob */

  val backup = "isabelle.in.tum.de:cronjob"
  val main_dir: Path = Path.explode("~/cronjob")
  val main_state_file: Path = main_dir + Path.explode("run/main.state")
  val build_release_log: Path = main_dir + Path.explode("run/build_release.log")
  val build_log_database_log: Path = main_dir + Path.explode("run/build_log_database.log")
  val current_log: Path = main_dir + Path.explode("run/main.log")  // owned by log service
  val cumulative_log: Path = main_dir + Path.explode("log/main.log")  // owned by log service
  val isabelle_repos: Path = main_dir + Path.explode("isabelle")
  val afp_repos: Path = main_dir + Path.explode("AFP")

  lazy val isabelle_hg: Mercurial.Repository = Mercurial.self_repository()
  lazy val afp_hg: Mercurial.Repository = Mercurial.repository(afp_repos)

  val mailman_archives_dir = Path.explode("~/cronjob/Mailman")

  val build_log_dirs =
    List(Path.explode("~/log"), Path.explode("~/afp/log"), Path.explode("~/cronjob/log"))

  val isabelle_devel: Path = Path.explode("/data/isatest/html-data/devel")
  val public_log: Path = Path.explode("/data/isatest/cronjob/run/main.log")  // owned by log service



  /** logger tasks **/

  sealed case class Logger_Task(name: String = "", body: Logger => Unit)


  /* init and exit */

  def get_rev(): String = isabelle_hg.id()
  def get_afp_rev(): String = afp_hg.id()

  val init: Logger_Task =
    Logger_Task("init",
      { logger =>
        val redirect = "https://isabelle-dev.sketis.net/home/menu/view/20"

        HTML.write_document(isabelle_devel, "index.html",
          List(
            XML.Elem(Markup("meta",
              List("http-equiv" -> "Refresh", "content" -> ("0; url=" + redirect))), Nil)),
          List(HTML.link(redirect, HTML.text("Isabelle Development Resources"))))

        Mercurial.setup_repository(Isabelle_System.afp_repository.root, afp_repos)

        File.write(logger.log_dir + Build_Log.log_filename("isabelle_identify", logger.start_date),
          Build_Log.Identify.content(logger.start_date, Some(get_rev()), Some(get_afp_rev())))

        Isabelle_System.bash(
          File.bash_path(Component_Rsync.local_program) +
            """ -a --include="*/" --include="plain_identify*" --exclude="*" """ +
            Bash.string(backup + "/log/.") + " " + File.bash_path(main_dir) + "/log/.").check

        val cronjob_log = isabelle_devel + Path.basic("cronjob-main.log")
        if (!cronjob_log.is_file) {
          Files.createSymbolicLink(cronjob_log.java_path, public_log.java_path)
        }
      })

  val exit: Logger_Task =
    Logger_Task("exit",
      { logger =>
        Isabelle_System.bash(
          File.bash_path(Component_Rsync.local_program) +
            " -a " + File.bash_path(main_dir) + "/log/." + " " + Bash.string(backup) + "/log/.")
            .check
      })


  /* Mailman archives */

  val mailman_archives: Logger_Task =
    Logger_Task("mailman_archives",
      { logger =>
        Mailman.Isabelle_Users.download(mailman_archives_dir)
        Mailman.Isabelle_Dev.download(mailman_archives_dir)
      })


  /* build release */

  val build_release: Logger_Task =
    Logger_Task("build_release", { logger =>
      build_release_log.file.delete
      val rev = get_rev()
      val afp_rev = get_afp_rev()
      val progress = new File_Progress(build_release_log)

      Isabelle_System.with_tmp_dir("isadist") { target_dir =>
        Isabelle_System.update_directory(isabelle_devel + Path.explode("release_snapshot"),
          { website_dir =>
            val context = Build_Release.Release_Context(target_dir, progress = progress)
            Build_Release.build_release_archive(context, rev)
            Build_Release.build_release(logger.options, context, afp_rev = afp_rev,
              build_sessions = List(Isabelle_System.default_logic()),
              website = Some(website_dir))
          }
        )
      }
    })


  /* remote build_history */

  sealed case class Remote_Build(
    description: String,
    host: String,
    user: String = "",
    port: Int = 0,
    history: Int = 0,
    history_base: String = "build_history_base",
    components_base: String = Components.dynamic_components_base,
    clean_components: Boolean = true,
    shared_isabelle_self: Boolean = false,
    java_heap: String = "",
    options: String = "",
    args: String = "",
    afp: Boolean = false,
    bulky: Boolean = false,
    more_hosts: List[String] = Nil,
    detect: PostgreSQL.Source = "",
    count: () => Int = () => 1
  ) {
    def active(): Boolean = count() > 0

    def open_session(options: Options): SSH.Session =
      SSH.open_session(options, host = host, user = user, port = port)

    def sql: PostgreSQL.Source =
      SQL.and(
        Build_Log.Prop.build_engine.equal(Build_History.engine),
        Build_Log.Prop.build_host.member(host :: more_hosts),
        if_proper(detect, SQL.enclose(detect)))

    def profile: Build_Status.Profile =
      Build_Status.Profile(description, history = history, afp = afp, bulky = bulky, sql = sql)

    def history(db: SQL.Database, days: Int = 0): Build_Log.History = {
      val rev = get_rev()
      val afp_rev = if (afp) Some(get_afp_rev()) else None
      val base_rev = isabelle_hg.id(history_base)
      val filter_nodes = isabelle_hg.graph().all_succs(List(base_rev)).toSet
      Build_Log.History.retrieve(db, days, rev, afp_rev, sql,
        entry => filter_nodes(entry.isabelle_version))
    }

    def pick(options: Options): Option[(String, Option[String])] = {
      val store = Build_Log.store(options)
      using(store.open_database()) { db =>
        def get(days: Int, gap: Int): Option[(String, Option[String])] = {
          val runs = history(db, days = days).unknown_runs(filter = run => run.length >= gap)
          Build_Log.History.Run.longest(runs).median.map(_.versions)
        }
        get(options.int("build_log_history") max history, 2) orElse
        get(300, 8) orElse
        get(3000, 32) orElse
        get(0, 1)
      }
    }

    def build_history_options: String =
      " -h " + Bash.string(host) + " " +
      if_proper(java_heap,
        "-e 'ISABELLE_TOOL_JAVA_OPTIONS=\"$ISABELLE_TOOL_JAVA_OPTIONS -Xmx" + java_heap + "\"' ") +
      options
  }

  val remote_builds_old: List[Remote_Build] =
    List(
      Remote_Build("Windows", "vmnipkow9", history = 90,
        components_base = "/cygdrive/d/isatest/contrib",
        options = "-m32 -M4" +
          " -e ISABELLE_OCAML=ocaml -e ISABELLE_OCAMLC=ocamlc -e ISABELLE_OCAML_SETUP=true" +
          " -e ISABELLE_GHC_SETUP=true" +
          " -e ISABELLE_SMLNJ=/usr/local/smlnj-110.81/bin/sml",
        args = "-a",
        detect =
          Build_Log.Settings.ML_PLATFORM.toString + " = " + SQL.string("x86-windows") + " OR " +
          Build_Log.Settings.ML_PLATFORM + " = " + SQL.string("x86_64_32-windows"),
        count = () => 2),
      Remote_Build("Windows", "vmnipkow9", history = 90,
        components_base = "/cygdrive/d/isatest/contrib",
        options = "-m64 -M4" +
          " -S /cygdrive/d/isatest/contrib" +
          " -e ISABELLE_OCAML=ocaml -e ISABELLE_OCAMLC=ocamlc -e ISABELLE_OCAML_SETUP=true" +
          " -e ISABELLE_GHC_SETUP=true" +
          " -e ISABELLE_SMLNJ=/usr/local/smlnj-110.81/bin/sml",
        args = "-a",
        detect = Build_Log.Settings.ML_PLATFORM.toString + " = " + SQL.string("x86_64-windows"),
        count = () => 2),
      Remote_Build("Linux A", "augsburg1",
        options = "-m32 -B -M4" +
          " -e ISABELLE_OCAML=ocaml -e ISABELLE_OCAMLC=ocamlc -e ISABELLE_OCAMLFIND=ocamlfind" +
          " -e ISABELLE_GHC_SETUP=true" +
          " -e ISABELLE_MLTON=mlton -e ISABELLE_MLTON_OPTIONS=" +
          " -e ISABELLE_SMLNJ=sml" +
          " -e ISABELLE_SWIPL=swipl",
        args = "-a -d '~~/src/Benchmarks'"),
      Remote_Build("macOS 10.15 Catalina", "laramac01", user = "makarius",
        options = "-m32 -M4 -e ISABELLE_GHC_SETUP=true -p pide_session=false",
        args = "-a -d '~~/src/Benchmarks'"),
      Remote_Build("Linux A", "i21of4", user = "i21isatest",
        options = "-m32 -M1x4,2,4" +
          " -e ISABELLE_OCAML=ocaml -e ISABELLE_OCAMLC=ocamlc -e ISABELLE_OCAML_SETUP=true" +
          " -e ISABELLE_GHC_SETUP=true" +
          " -e ISABELLE_MLTON=mlton" +
          " -e ISABELLE_SMLNJ=sml" +
          " -e ISABELLE_SWIPL=swipl",
        args = "-a -d '~~/src/Benchmarks'"),
      Remote_Build("Linux A", "lxbroy9",
        java_heap = "2g", options = "-m32 -B -M1x2,2", args = "-N -g timing"),
      Remote_Build("Linux Benchmarks", "lxbroy5", history = 90,
        java_heap = "2g",
        options = "-m32 -B -M1x2,2 -t Benchmarks" +
          " -e ISABELLE_GHC=ghc -e ISABELLE_MLTON=mlton -e ISABELLE_OCAML=ocaml" +
          " -e ISABELLE_OCAMLC=ocamlc -e ISABELLE_OCAMLFIND=ocamlfind -e ISABELLE_SMLNJ=sml" +
          " -e ISABELLE_SWIPL=swipl",
        args = "-N -a -d '~~/src/Benchmarks'",
        detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("Benchmarks")),
      Remote_Build("macOS 10.14 Mojave (Old)", "lapnipkow3",
        options = "-m32 -M1,2 -e ISABELLE_GHC_SETUP=true -p pide_session=false",
        args = "-a -d '~~/src/Benchmarks'"),
      Remote_Build("AFP old bulky", "lrzcloud1",
        options = "-m64 -M6 -U30000 -s10 -t AFP",
        args = "-g large -g slow",
        afp = true,
        bulky = true,
        detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("AFP")),
      Remote_Build("AFP old", "lxbroy7",
          args = "-N -X large -X slow",
          afp = true,
          detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("AFP")),
      Remote_Build("AFP old2", "lrzcloud2", history = 120,
        java_heap = "8g",
        options = "-m32 -M1x5 -t AFP" +
          " -e ISABELLE_GHC=ghc" +
          " -e ISABELLE_MLTON=mlton -e ISABELLE_MLTON_OPTIONS=" +
          " -e ISABELLE_OCAML=ocaml -e ISABELLE_OCAMLC=ocamlc -e ISABELLE_OCAMLFIND=ocamlfind" +
          " -e ISABELLE_SMLNJ=sml",
        args = "-a -X large -X slow",
        afp = true,
        detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("AFP"),
        count = () => if (Date.now().unix_epoch_day % 2 == 0) 1 else 0),
      Remote_Build("AFP old2", "lrzcloud2",
        java_heap = "8g",
        options = "-m64 -M8 -U30000 -s10 -t AFP",
        args = "-g large -g slow",
        afp = true,
        bulky = true,
        detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("AFP"),
        count = () => if (Date.now().unix_epoch_day % 2 == 1) 1 else 0),
      Remote_Build("Poly/ML 5.7 Linux", "lxbroy8",
        history_base = "37074e22e8be",
        options = "-m32 -B -M1x2,2 -t polyml-5.7 -i 'init_component /home/isabelle/contrib/polyml-5.7'",
        args = "-N -g timing",
        detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("polyml-5.7") + " AND " +
          Build_Log.Settings.ML_OPTIONS + " <> " + SQL.string("-H 500")),
      Remote_Build("Poly/ML 5.7.1 Linux", "lxbroy8",
        history_base = "a9d5b59c3e12",
        options = "-m32 -B -M1x2,2 -t polyml-5.7.1-pre2 -i 'init_component /home/isabelle/contrib/polyml-test-905dae2ebfda'",
        args = "-N -g timing",
        detect =
          Build_Log.Prop.build_tags.toString + " = " + SQL.string("polyml-5.7.1-pre1") + " OR " +
          Build_Log.Prop.build_tags + " = " + SQL.string("polyml-5.7.1-pre2")),
      Remote_Build("Poly/ML 5.7 macOS", "macbroy2",
        history_base = "37074e22e8be",
        options = "-m32 -B -M1x4,4 -t polyml-5.7 -i 'init_component /home/isabelle/contrib/polyml-5.7'",
        args = "-a",
        detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("polyml-5.7")),
      Remote_Build("Poly/ML 5.7.1 macOS", "macbroy2",
        history_base = "a9d5b59c3e12",
        options = "-m32 -B -M1x4,4 -t polyml-5.7.1-pre2 -i 'init_component /home/isabelle/contrib/polyml-test-905dae2ebfda'",
        args = "-a",
        detect =
          Build_Log.Prop.build_tags.toString + " = " + SQL.string("polyml-5.7.1-pre1") + " OR " +
          Build_Log.Prop.build_tags + " = " + SQL.string("polyml-5.7.1-pre2")),
      Remote_Build("macOS", "macbroy2",
        options = "-m32 -M8" +
          " -e ISABELLE_GHC=ghc -e ISABELLE_MLTON=mlton -e ISABELLE_OCAML=ocaml" +
          " -e ISABELLE_OCAMLC=ocamlc -e ISABELLE_OCAML_SETUP=true" +
          " -e ISABELLE_OPAM_ROOT=\"$ISABELLE_HOME/opam\"" +
          " -e ISABELLE_SMLNJ=/home/isabelle/smlnj/110.85/bin/sml" +
          " -p pide_session=false",
        args = "-a",
        detect = Build_Log.Prop.build_tags.undefined,
        history_base = "2c0f24e927dd"),
      Remote_Build("macOS, quick_and_dirty", "macbroy2",
        options = "-m32 -M8 -t quick_and_dirty -p pide_session=false", args = "-a -o quick_and_dirty",
        detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("quick_and_dirty"),
        history_base = "2c0f24e927dd"),
      Remote_Build("macOS, skip_proofs", "macbroy2",
        options = "-m32 -M8 -t skip_proofs -p pide_session=false", args = "-a -o skip_proofs",
        detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("skip_proofs"),
        history_base = "2c0f24e927dd"),
      Remote_Build("Poly/ML test", "lxbroy8",
        options = "-m32 -B -M1x2,2 -t polyml-test -i 'init_component /home/isabelle/contrib/polyml-5.7-20170217'",
        args = "-N -g timing",
        detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("polyml-test")),
      Remote_Build("macOS 10.12 Sierra", "macbroy30", options = "-m32 -M2 -p pide_session=false", args = "-a",
        detect = Build_Log.Prop.build_start.toString + " > date '2017-03-03'"),
      Remote_Build("macOS 10.10 Yosemite", "macbroy31", options = "-m32 -M2 -p pide_session=false", args = "-a"),
      Remote_Build("macOS 10.8 Mountain Lion", "macbroy30", options = "-m32 -M2", args = "-a",
        detect = Build_Log.Prop.build_start.toString + " < date '2017-03-03'")) :::
      {
        for ((n, hosts) <- List(1 -> List("lxbroy6"), 2 -> List("lxbroy8", "lxbroy5")))
        yield {
          Remote_Build("AFP old", host = hosts.head, more_hosts = hosts.tail,
            options = "-m32 -M1x2 -t AFP -P" + n +
              " -e ISABELLE_GHC=ghc" +
              " -e ISABELLE_MLTON=mlton" +
              " -e ISABELLE_OCAML=ocaml -e ISABELLE_OCAMLC=ocamlc -e ISABELLE_OCAMLFIND=ocamlfind" +
              " -e ISABELLE_SMLNJ=sml",
            args = "-N -X large -X slow",
            afp = true,
            detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("AFP"))
        }
      }

  val remote_builds1: List[List[Remote_Build]] = {
    List(
      List(Remote_Build("Linux (ARM)", "linux-arm",
        history_base = "build_history_base_arm",
        clean_components = false,
        shared_isabelle_self = true,
        options = "-m32 -B -M1x2 -U 4000 -p timeout_scale=2" +
          " -e ISABELLE_SWIPL=swipl",
        args = "-a -d '~~/src/Benchmarks'")),
      List(Remote_Build("Linux B", "lxbroy10", history = 90,
        options = "-m32 -B -M1x4,2,4,6", args = "-N -g timing")),
      List(
        Remote_Build("macOS 12 Monterey (Intel)", "mini1-monterey",
          options = "-m32 -B -M1x2,2,4 -p pide_session=false" +
            " -e ISABELLE_OCAML=ocaml -e ISABELLE_OCAMLC=ocamlc -e ISABELLE_OCAML_SETUP=true" +
            " -e ISABELLE_GHC_SETUP=true" +
            " -e ISABELLE_MLTON=/usr/local/bin/mlton -e ISABELLE_MLTON_OPTIONS=" +
            " -e ISABELLE_SMLNJ=/usr/local/smlnj/bin/sml" +
            " -e ISABELLE_SWIPL=/usr/local/bin/swipl",
          args = "-a -d '~~/src/Benchmarks'")),
      List(
        Remote_Build("AFP macOS (macOS 14 Sonoma, Apple Silicon)", "studio1-sonoma", history = 120,
          history_base = "build_history_base_arm",
          java_heap = "8g",
          options = "-m32 -M1x5 -p pide_session=false -t AFP" +
            " -e ISABELLE_GHC_SETUP=true" +
            " -e ISABELLE_GO_SETUP=true" +
            " -e ISABELLE_SMLNJ=/usr/local/smlnj/bin/sml" +
            " -e ISABELLE_SWIPL=/opt/homebrew/bin/swipl",
          args = "-a -d '~~/src/Benchmarks' -X large -X slow",
          afp = true,
          detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("AFP"))),
      List(
        Remote_Build("macOS 14 Sonoma, quick_and_dirty", "mini2-sonoma",
          options = "-m32 -M4 -t quick_and_dirty -p pide_session=false",
          args = "-a -o quick_and_dirty",
          detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("quick_and_dirty"),
          count = () => 1),
        Remote_Build("macOS 14 Sonoma, skip_proofs", "mini2-sonoma",
          options = "-m32 -M4 -t skip_proofs -p pide_session=false", args = "-a -o skip_proofs",
          detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("skip_proofs"),
          count = () => 1)),
      List(
        Remote_Build("macOS 13 Ventura (ARM)", "mini3",
          history_base = "build_history_base_arm",
          options = "-a -m32 -B -M1x4,2x2,4 -p pide_session=false" +
            " -e ISABELLE_GHC_SETUP=true" +
            " -e ISABELLE_MLTON=/opt/homebrew/bin/mlton -e ISABELLE_MLTON_OPTIONS=" +
            " -e ISABELLE_SWIPL=/opt/homebrew/bin/swipl",
          args = "-a -d '~~/src/Benchmarks'",
          count = () => 3)),
      List(
        Remote_Build("AFP Windows", "windows2",
          java_heap = "8g",
          options = "-m32 -M1x5 -t AFP",
          args = "-a -X large -X slow",
          afp = true,
          detect = Build_Log.Prop.build_tags.toString + " = " + SQL.string("AFP")))
    )
  }

  val remote_builds2: List[List[Remote_Build]] =
    List()

  def remote_build_history(
    rev: String,
    afp_rev: Option[String],
    i: Int,
    r: Remote_Build,
    progress: Progress = new Progress
  ) : Logger_Task = {
    val task_name = "build_history-" + r.host
    Logger_Task(task_name,
      { logger =>
        using(r.open_session(logger.options)) { ssh =>
          val results =
            Build_History.remote_build(ssh,
              isabelle_repos,
              isabelle_repos.ext(r.host),
              isabelle_identifier = "cronjob_build_history",
              components_base = r.components_base,
              clean_platform = r.clean_components,
              clean_archives = r.clean_components,
              shared_isabelle_self = r.shared_isabelle_self,
              rev = rev,
              afp_repos = if (afp_rev.isDefined) Some(afp_repos) else None,
              afp_rev = afp_rev.getOrElse(""),
              options =
                " -N " + Bash.string(task_name) + (if (i < 0) "" else "_" + (i + 1).toString) +
                " -f " + r.build_history_options,

              args = "-o timeout=10800 " + r.args)

          val log_files =
            for ((log_name, bytes) <- results) yield {
              val log_file = logger.log_dir + Path.explode(log_name)
              logger.log(Date.now(), log_name)
              Bytes.write(log_file, bytes)
              log_file
            }

          Build_Log.build_log_database(logger.options, log_files,
            progress = progress, ml_statistics = true)
        }
      })
  }

  val build_status_profiles: List[Build_Status.Profile] =
    (remote_builds_old :: remote_builds1 ::: remote_builds2).flatten.map(_.profile)



  /** task logging **/

  object Log_Service {
    def apply(options: Options, progress: Progress = new Progress): Log_Service =
      new Log_Service(options, progress)
  }

  class Log_Service private(val options: Options, progress: Progress) {
    current_log.file.delete

    private val thread: Consumer_Thread[String] =
      Consumer_Thread.fork("cronjob: logger", daemon = true)(
        consume =
          { (text: String) =>
            // critical
            File.append(current_log, text + "\n")
            File.append(cumulative_log, text + "\n")
            progress.echo(text)
            true
          })

    def shutdown(): Unit = { thread.shutdown() }

    val hostname: String = Isabelle_System.hostname()

    def log(date: Date, task_name: String, msg: String): Unit =
      if (task_name.nonEmpty) {
        thread.send(
          "[" + Build_Log.print_date(date) + ", " + hostname + ", " + task_name + "]: " + msg)
      }

    def start_logger(start_date: Date, task_name: String): Logger =
      new Logger(this, start_date, task_name)

    def run_task(start_date: Date, task: Logger_Task): Unit = {
      val logger = start_logger(start_date, task.name)
      val res = Exn.result { task.body(logger) }
      val end_date = Date.now()
      val err =
        res match {
          case Exn.Res(_) => None
          case Exn.Exn(exn) =>
            Output.writeln("Exception trace for " + quote(task.name) + ":\n" +
              Exn.message(exn) + "\n" + Exn.trace(exn))
            val first_line = split_lines(Exn.message(exn)).headOption getOrElse "exception"
            Some(first_line)
        }
      logger.log_end(end_date, err)
    }

    def fork_task(start_date: Date, task: Logger_Task): Task =
      new Task(task.name, run_task(start_date, task))
  }

  class Logger private[Isabelle_Cronjob](
    log_service: Log_Service,
    val start_date: Date,
    val task_name: String
  ) {
    def options: Options = log_service.options

    def log(date: Date, msg: String): Unit = log_service.log(date, task_name, msg)

    def log_end(end_date: Date, err: Option[String]): Unit = {
      val elapsed_time = end_date - start_date
      val msg =
        (if (err.isEmpty) "finished" else "ERROR " + err.get) +
        (if (elapsed_time.seconds < 3.0) "" else " (" + elapsed_time.message_hms + " elapsed time)")
      log(end_date, msg)
    }

    val log_dir: Path = Isabelle_System.make_directory(main_dir + Build_Log.log_subdir(start_date))

    log(start_date, "started")
  }

  class Task private[Isabelle_Cronjob](name: String, body: => Unit) {
    private val future: Future[Unit] = Future.thread("cronjob: " + name) { body }
    def is_finished: Boolean = future.is_finished
  }



  /** cronjob **/

  def cronjob(progress: Progress, exclude_task: Set[String]): Unit = {
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

    val log_service = Log_Service(Options.init(), progress = progress)

    def run(start_date: Date, task: Logger_Task): Unit = log_service.run_task(start_date, task)

    def run_now(task: Logger_Task): Unit = run(Date.now(), task)


    /* structured tasks */

    def SEQ(tasks: List[() => Option[Logger_Task]]): Logger_Task =
      Logger_Task(body = _ =>
        for {
          t <- tasks.iterator
          task <- t()
          if !exclude_task(task.name) || task.name.isEmpty
        } run_now(task))

    def SEQUENTIAL(tasks: Logger_Task*): Logger_Task =
      SEQ(List.from(for (task <- tasks.iterator) yield () => Some(task)))

    def PAR(tasks: List[Logger_Task]): Logger_Task =
      Logger_Task(body =
        { _ =>
          @tailrec def join(running: List[Task]): Unit = {
            running.partition(_.is_finished) match {
              case (Nil, Nil) =>
              case (Nil, _ :: _) => Time.seconds(0.5).sleep(); join(running)
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
    File.write(main_state_file, main_start_date.toString + " " + log_service.hostname)

    val build_log_database_progress = new File_Progress(build_log_database_log, verbose = true)
    build_log_database_progress.echo(
      "Started at " + Build_Log.print_date(build_log_database_progress.start))

    run(main_start_date,
      Logger_Task("isabelle_cronjob", logger =>
        run_now(
          SEQUENTIAL(
            init,
            PAR(
              List(
                mailman_archives,
                build_release,
                Logger_Task("build_log_database",
                  logger =>
                    Build_Log.build_log_database(logger.options, build_log_dirs,
                      progress = build_log_database_progress,
                      vacuum = true, ml_statistics = true,
                      snapshot = Some(isabelle_devel + Path.explode("build_log.db")))))),
            PAR(
              List(remote_builds1, remote_builds2).map(remote_builds =>
                SEQUENTIAL(
                  PAR(remote_builds.map(seq =>
                    SEQ(
                      for {
                        (r, i) <- (if (seq.length <= 1) seq.map((_, -1)) else seq.zipWithIndex)
                        _ <- List.from(1 to r.count())
                      } yield () => {
                        r.pick(logger.options)
                          .map({ case (rev, afp_rev) =>
                            remote_build_history(rev, afp_rev, i, r,
                              progress = build_log_database_progress) })
                      }
                    ))),
                  Logger_Task("build_status", logger =>
                    Isabelle_System.update_directory(
                      isabelle_devel + Path.explode("build_status"),
                      dir =>
                        Build_Status.build_status(logger.options,
                          target_dir = dir, ml_statistics = true)))))),
            exit))))

    log_service.shutdown()

    main_state_file.file.delete
  }



  /** command line entry point **/

  def main(args: Array[String]): Unit = {
    Command_Line.tool {
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

      val progress = if (verbose) new Console_Progress() else new Progress

      if (force) cronjob(progress, exclude_task)
      else error("Need to apply force to do anything")
    }
  }
}
