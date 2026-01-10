/*  Title:      Pure/Build/build.scala
    Author:     Makarius
    Options:    :folding=explicit:

Command-line tools to build and manage Isabelle sessions.
*/

package isabelle

import scala.collection.mutable
import scala.util.matching.Regex


object Build {
  /** "isabelle build" **/

  /* options */

  def hostname(options: Options): String =
    Isabelle_System.hostname(options.string("build_hostname"))

  def engine_name(options: Options): String = options.string("build_engine")


  /* context */

  sealed case class Context(
    store: Store,
    deps: isabelle.Sessions.Deps,
    engine: Engine = Engine.Default,
    afp_root: Option[Path] = None,
    build_hosts: List[Build_Cluster.Host] = Nil,
    hostname: String = Isabelle_System.hostname(),
    numa_shuffling: Boolean = false,
    numa_nodes: List[Int] = Nil,
    clean_sessions: List[String] = Nil,
    store_heap: Boolean = false,
    fresh_build: Boolean = false,
    no_build: Boolean = false,
    session_setup: (String, Session) => Unit = (_, _) => (),
    build_uuid: String = UUID.random_string(),
    build_start: Option[Date] = None,
    jobs: Int = 0,
    master: Boolean = false
  ) {
    def build_options: Options = store.options

    def ml_platform: String = store.ml_settings.ml_platform

    def sessions_structure: isabelle.Sessions.Structure = deps.sessions_structure

    def worker: Boolean = jobs > 0

    override def toString: String =
      "Build.Context(build_uuid = " + quote(build_uuid) +
        if_proper(worker, ", worker = true") +
        if_proper(master, ", master = true") + ")"
  }


  /* results */

  object Results {
    def apply(
      context: Context,
      results: Map[String, Process_Result] = Map.empty,
      other_rc: Int = Process_Result.RC.ok
    ): Results = {
      new Results(context.store, context.deps, results, other_rc)
    }
  }

  class Results private(
    val store: Store,
    val deps: Sessions.Deps,
    results: Map[String, Process_Result],
    other_rc: Int
  ) {
    def cache: Rich_Text.Cache = store.cache

    def sessions_ok: List[String] =
      List.from(
        for {
          name <- deps.sessions_structure.build_topological_order.iterator
          result <- results.get(name) if result.ok
        } yield name)

    def info(name: String): Sessions.Info = deps.sessions_structure(name)
    def sessions: Set[String] = results.keySet
    def cancelled(name: String): Boolean = !results(name).defined
    def apply(name: String): Process_Result = results(name).strict

    val rc: Int =
      Process_Result.RC.merge(other_rc,
        Process_Result.RC.merge(results.valuesIterator.map(_.strict.rc)))
    def ok: Boolean = rc == Process_Result.RC.ok

    lazy val unfinished: List[String] = sessions.iterator.filterNot(apply(_).ok).toList.sorted

    def check: Results =
      if (ok) this
      else if (unfinished.isEmpty) error("Build failed")
      else error("Build failed with unfinished session(s): " + commas(unfinished))

    override def toString: String = rc.toString
  }


  /* engine */

  object Engine {
    lazy val services: List[Engine] =
      Isabelle_System.make_services(classOf[Engine])

    def apply(name: String): Engine =
      services.find(_.name == name).getOrElse(error("Bad build engine " + quote(name)))

    class Default extends Engine("") { override def toString: String = "<default>" }
    object Default extends Default
  }

  class Engine(val name: String) extends Isabelle_System.Service {
    engine =>

    override def toString: String = name

    def build_options(options: Options, build_cluster: Boolean = false): Options = {
      val options1 = options + "completion_limit=0" + "editor_tracing_messages=0"
      if (build_cluster) options1 + "build_database" + "build_database_server" + "build_log_verbose" else options1  // FIXME tmp: build_database_server
    }

    final def build_store(options: Options,
      private_dir: Option[Path] = None,
      build_cluster: Boolean = false,
      cache: Rich_Text.Cache = Rich_Text.Cache.make()
    ): Store = {
      val build_options = engine.build_options(options, build_cluster = build_cluster)
      val store =
        Store(build_options,
          private_dir = private_dir,
          build_cluster = build_cluster,
          cache = cache)
      Isabelle_System.make_directory(store.output_dir + Path.basic("log"))
      Isabelle_Fonts.init()
      store
    }

    def open_build_process(
      build_context: Context,
      build_progress: Progress,
      server: SSH.Server
    ): Build_Process = new Build_Process(build_context, build_progress, server)

    final def run_build_process(
      context: Context,
      progress: Progress,
      server: SSH.Server
    ): Results = {
      Isabelle_Thread.uninterruptible {
        using(open_build_process(context, progress, server)) { build_process =>
          build_process.prepare()
          build_process.run()
        }
      }
    }
  }



  /* build */

  def progress_threshold(options: Options): Time = options.seconds("build_progress_threshold")
  def progress_detailed(options: Options): Boolean = options.bool("build_progress_detailed")

  def build(
    options: Options,
    private_dir: Option[Path] = None,
    build_hosts: List[Build_Cluster.Host] = Nil,
    selection: Sessions.Selection = Sessions.Selection.empty,
    browser_info: Browser_Info.Config = Browser_Info.Config.none,
    progress: Progress = new Progress,
    check_unknown_files: Boolean = false,
    build_heap: Boolean = false,
    clean_build: Boolean = false,
    afp_root: Option[Path] = None,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    infos: List[Sessions.Info] = Nil,
    numa_shuffling: Boolean = false,
    max_jobs: Option[Int] = None,
    list_files: Boolean = false,
    fresh_build: Boolean = false,
    no_build: Boolean = false,
    soft_build: Boolean = false,
    export_files: Boolean = false,
    augment_options: String => List[Options.Spec] = _ => Nil,
    session_setup: (String, Session) => Unit = (_, _) => (),
    cache: Rich_Text.Cache = Rich_Text.Cache.make()
  ): Results = {
    val engine = Engine(engine_name(options))
    val store =
      engine.build_store(options,
        private_dir = private_dir,
        build_cluster = build_hosts.nonEmpty,
        cache = cache)
    val build_options = store.options

    using(store.open_server()) { server =>

      /* session selection and dependencies */

      val full_sessions =
        Sessions.load_structure(build_options, dirs = AFP.main_dirs(afp_root) ::: dirs,
          select_dirs = select_dirs, infos = infos, augment_options = augment_options)
      val selected_sessions = full_sessions.imports_selection(selection)

      val build_deps = {
        val deps0 =
          Sessions.deps(full_sessions.selection(selection), progress = progress,
            inlined_files = true, list_files = list_files).check_errors

        if (soft_build && !fresh_build) {
          val outdated =
            deps0.sessions_structure.build_topological_order.flatMap(name =>
              store.try_open_database(name, server = server) match {
                case Some(db) =>
                  using(db)(store.read_build(_, name)) match {
                    case Some(build) if build.ok =>
                      val sources_shasum = deps0.sources_shasum(name)
                      val thorough = deps0.sessions_structure(name).build_thorough
                      if (Sessions.eq_sources(thorough, build.sources, sources_shasum)) None
                      else Some(name)
                    case _ => Some(name)
                  }
                case None => Some(name)
              })

          Sessions.deps(full_sessions.selection(Sessions.Selection(sessions = outdated)),
            progress = progress, inlined_files = true).check_errors
        }
        else deps0
      }


      /* check unknown files */

      if (check_unknown_files) {
        val source_files =
          List.from(
            for {
              (_, base) <- build_deps.session_bases.iterator
              (path, _) <- base.session_sources.iterator
            } yield path)
        Mercurial.check_files(source_files)._2 match {
          case Nil =>
          case unknown_files =>
            progress.echo_warning(
              "Unknown files (not part of the underlying Mercurial repository):" +
              unknown_files.map(File.standard_path).sorted.mkString("\n  ", "\n  ", ""))
        }
      }


      /* build process and results */

      val clean_sessions =
        if (clean_build) full_sessions.imports_descendants(selected_sessions) else Nil

      val numa_nodes = Host.numa_nodes(enabled = numa_shuffling)
      val build_context =
        Context(store, build_deps, engine = engine, afp_root = afp_root,
          build_hosts = build_hosts, hostname = hostname(build_options),
          clean_sessions = clean_sessions, store_heap = build_heap,
          numa_shuffling = numa_shuffling, numa_nodes = numa_nodes,
          fresh_build = fresh_build, no_build = no_build, session_setup = session_setup,
          jobs = max_jobs.getOrElse(if (build_hosts.nonEmpty) 0 else 1), master = true)

      val results = engine.run_build_process(build_context, progress, server)

      if (export_files) {
        for (name <- selected_sessions.iterator if results(name).ok) {
          val info = results.info(name)
          if (info.export_files.nonEmpty) {
            progress.echo("Exporting " + info.name + " ...")
            for ((dir, prune, pats) <- info.export_files) {
              Export.export_files(store, name, info.dir + dir,
                progress = if (progress.verbose) progress else new Progress,
                export_prune = prune,
                export_patterns = pats)
            }
          }
        }
      }

      val presentation_sessions =
        results.sessions_ok.filter(name => browser_info.enabled(results.info(name)))
      if (presentation_sessions.nonEmpty && !progress.stopped) {
        Browser_Info.build(browser_info, results.store, results.deps, presentation_sessions,
          progress = progress, server = server)
      }

      if (results.unfinished.nonEmpty && (progress.verbose || !no_build)) {
        progress.echo("Unfinished session(s): " + commas(results.unfinished))
      }

      results
    }
  }


  /* build logic image */

  def build_logic_started(logic: String): String =
    "Build started for Isabelle/" + logic + " ..."

  def build_logic_failed(logic: String, editor: Boolean = false): String =
    "Failed to build Isabelle/" + logic + if_proper(editor, " -- prover process remains inactive!")

  def build_logic(options: Options, logic: String,
    private_dir: Option[Path] = None,
    progress: Progress = new Progress,
    build_heap: Boolean = false,
    dirs: List[Path] = Nil,
    fresh: Boolean = false,
    strict: Boolean = false
  ): Results = {
    val selection = Sessions.Selection.session(logic)

    def test_build(): Results =
      build(options, selection = selection,
        build_heap = build_heap, no_build = true, dirs = dirs)

    def full_build(): Results = {
      progress.echo(build_logic_started(logic))
      build(options, selection = selection, progress = progress,
        build_heap = build_heap, fresh_build = fresh, dirs = dirs)
    }

    val results =
      progress.interrupt_handler {
        if (fresh) full_build()
        else {
          val test_results = test_build()
          if (test_results.ok) test_results else full_build()
        }
      }

    if (strict && !results.ok) error(build_logic_failed(logic)) else results
  }


  /* Isabelle tool wrappers */

  val isabelle_tool1 = Isabelle_Tool("build", "build and manage Isabelle sessions",
    Scala_Project.here,
    { args =>
      var afp_root: Option[Path] = None
      val base_sessions = new mutable.ListBuffer[String]
      val select_dirs = new mutable.ListBuffer[Path]
      val build_hosts = new mutable.ListBuffer[Build_Cluster.Host]
      var numa_shuffling = false
      var browser_info = Browser_Info.Config.none
      var requirements = false
      var soft_build = false
      val exclude_session_groups = new mutable.ListBuffer[String]
      var all_sessions = false
      var build_heap = false
      var clean_build = false
      val dirs = new mutable.ListBuffer[Path]
      var export_files = false
      var fresh_build = false
      val session_groups = new mutable.ListBuffer[String]
      var max_jobs: Option[Int] = None
      var list_files = false
      var no_build = false
      var options = Options.init(specs = Options.Spec.ISABELLE_BUILD_OPTIONS)
      var verbose = false
      val exclude_sessions = new mutable.ListBuffer[String]

      val getopts = Getopts("""
Usage: isabelle build [OPTIONS] [SESSIONS ...]

  Options are:
    -A ROOT      include AFP with given root directory (":" for """ + AFP.BASE.implode + """)
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -H HOSTS     additional cluster host specifications of the form
                 NAMES:PARAMETERS (separated by commas)
    -N           cyclic shuffling of NUMA CPU nodes (performance tuning)
    -P DIR       enable HTML/PDF presentation in directory (":" for default)
    -R           refer to requirements of selected sessions
    -S           soft build: only observe changes of sources, not heap images
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -b           build heap images
    -c           clean build
    -d DIR       include session directory
    -e           export files from session specification into file-system
    -f           fresh build
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs
                 (default: 1 for local build, 0 for build cluster)
    -l           list session source files
    -n           no build -- take existing session build databases
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Build and manage Isabelle sessions: ML heaps, session databases, documents.

  Parameters for cluster host specifications (-H), apart from system options:
""" + Library.indent_lines(4, Build_Cluster.Host.parameters.print()) +
"""

  Notable system options: see "isabelle options -l -t build"

  Notable system settings:
""" + Library.indent_lines(4, Build_Log.Settings.show(ML_Settings(options))) + "\n",
        "A:" -> (arg => afp_root = Some(if (arg == ":") AFP.BASE else Path.explode(arg))),
        "B:" -> (arg => base_sessions += arg),
        "D:" -> (arg => select_dirs += Path.explode(arg)),
        "H:" -> (arg => build_hosts ++= Build_Cluster.Host.parse(Registry.global, arg)),
        "N" -> (_ => numa_shuffling = true),
        "P:" -> (arg => browser_info = Browser_Info.Config.make(arg)),
        "R" -> (_ => requirements = true),
        "S" -> (_ => soft_build = true),
        "X:" -> (arg => exclude_session_groups += arg),
        "a" -> (_ => all_sessions = true),
        "b" -> (_ => build_heap = true),
        "c" -> (_ => clean_build = true),
        "d:" -> (arg => dirs += Path.explode(arg)),
        "e" -> (_ => export_files = true),
        "f" -> (_ => fresh_build = true),
        "g:" -> (arg => session_groups += arg),
        "j:" -> (arg => max_jobs = Some(Value.Nat.parse(arg))),
        "l" -> (_ => list_files = true),
        "n" -> (_ => no_build = true),
        "o:" -> (arg => options = options + arg),
        "v" -> (_ => verbose = true),
        "x:" -> (arg => exclude_sessions += arg))

      val sessions = getopts(args)

      val progress =
        new Console_Progress(verbose = verbose,
          threshold = progress_threshold(options),
          detailed = progress_detailed(options))

      val ml_settings = ML_Settings(options)

      progress.echo(
        "Started at " + Build_Log.print_date(progress.start) +
          " (" + ml_settings.ml_identifier + " on " + hostname(options) +")",
        verbose = true)
      progress.echo(Build_Log.Settings.show(ml_settings) + "\n", verbose = true)

      val results =
        progress.interrupt_handler {
          build(options,
            selection = Sessions.Selection(
              requirements = requirements,
              all_sessions = all_sessions,
              base_sessions = base_sessions.toList,
              exclude_session_groups = exclude_session_groups.toList,
              exclude_sessions = exclude_sessions.toList,
              session_groups = session_groups.toList,
              sessions = sessions),
            browser_info = browser_info,
            progress = progress,
            check_unknown_files = Mercurial.is_repository(Path.ISABELLE_HOME),
            build_heap = build_heap,
            clean_build = clean_build,
            afp_root = afp_root,
            dirs = dirs.toList,
            select_dirs = select_dirs.toList,
            numa_shuffling = Host.numa_check(progress, numa_shuffling),
            max_jobs = max_jobs,
            list_files = list_files,
            fresh_build = fresh_build,
            no_build = no_build,
            soft_build = soft_build,
            export_files = export_files,
            build_hosts = build_hosts.toList)
        }
      val stop_date = progress.now()
      val elapsed_time = stop_date - progress.start

      progress.echo("\nFinished at " + Build_Log.print_date(stop_date), verbose = true)

      val total_timing =
        results.sessions.iterator.map(a => results(a).timing).foldLeft(Timing.zero)(_ + _).
          copy(elapsed = elapsed_time)
      progress.echo(total_timing.message_resources)

      sys.exit(results.rc)
    })



  /** build cluster management **/

  /* identified builds */

  def read_builds(build_database: Option[SQL.Database]): List[Build_Process.Build] =
    build_database match {
      case None => Nil
      case Some(db) => Build_Process.read_builds(db)
    }

  def print_builds(build_database: Option[SQL.Database], builds: List[Build_Process.Build]): String =
  {
    val print_database =
      build_database match {
        case None => ""
        case Some(db) => " (database " + db + ")"
      }
    if (builds.isEmpty) "No build processes" + print_database
    else "Build processes" + print_database + builds.map(build => "\n  " + build.print).mkString
  }

  def find_builds(
    build_database: Option[SQL.Database],
    build_id: String,
    builds: List[Build_Process.Build]
  ): Build_Process.Build = {
    (build_id, builds.length) match {
      case (UUID(_), _) if builds.exists(_.build_uuid == build_id) =>
        builds.find(_.build_uuid == build_id).get
      case ("", 1) => builds.head
      case ("", 0) => error(print_builds(build_database, builds))
      case _ =>
        cat_error("Cannot identify build process " + quote(build_id),
          print_builds(build_database, builds))
    }
  }


  /* "isabelle build_process" */

  def build_process(
    options: Options,
    build_cluster: Boolean = false,
    list_builds: Boolean = false,
    remove_builds: Boolean = false,
    force: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    val engine = Engine(engine_name(options))
    val store = engine.build_store(options, build_cluster = build_cluster)

    using(store.open_server()) { server =>
      using_optional(store.maybe_open_build_database(server = server)) { build_database =>
        def print(builds: List[Build_Process.Build]): Unit =
          if (list_builds) progress.echo(print_builds(build_database, builds))

        build_database match {
          case None => print(Nil)
          case Some(db) if remove_builds && force =>
            db.transaction {
              val tables0 =
                ML_Heap.private_data.tables.list :::
                Store.private_data.tables.list :::
                Database_Progress.private_data.tables.list :::
                Build_Process.private_data.tables.list
              val tables = tables0.filter(t => db.exists_table(t.name)).sortBy(_.name)
              if (tables.nonEmpty) {
                progress.echo("Removing tables " + commas_quote(tables.map(_.name)) + " ...")
                db.execute_statement(SQL.MULTI(tables.map(db.destroy)))
              }
            }
          case Some(db) =>
            Build_Process.private_data.transaction_lock(db, create = true, label = "build_process") {
              val builds = Build_Process.private_data.read_builds(db)
              print(builds)
              if (remove_builds) {
                val remove = builds.flatMap(_.active_build_uuid)
                if (remove.nonEmpty) {
                  progress.echo("Removing " + commas(remove) + " ...")
                  Build_Process.private_data.remove_builds(db, remove)
                  print(Build_Process.private_data.read_builds(db))
                }
              }
            }
        }
      }
    }
  }

  val isabelle_tool2 = Isabelle_Tool("build_process", "manage session build process",
    Scala_Project.here,
    { args =>
      var build_cluster = false
      var force = false
      var list_builds = false
      var options =
        Options.init(specs =
          Options.Spec.ISABELLE_BUILD_OPTIONS ::: List(Options.Spec.make("build_database")))
      var remove_builds = false

      val getopts = Getopts("""
Usage: isabelle build_process [OPTIONS]

  Options are:
    -C           build cluster mode (database server)
    -f           extra force for option -r
    -l           list build processes
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -r           remove data from build processes: inactive processes (default)
                 or all processes (option -f)

  Manage Isabelle build process, notably distributed build cluster (option -C).
""",
        "C" -> (_ => build_cluster = true),
        "f" -> (_ => force = true),
        "l" -> (_ => list_builds = true),
        "o:" -> (arg => options = options + arg),
        "r" -> (_ => remove_builds = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      build_process(options, build_cluster = build_cluster, list_builds = list_builds,
        remove_builds = remove_builds, force = force, progress = progress)
    })



  /* "isabelle build_worker" */

  def build_worker_command(
    host: Build_Cluster.Host,
    ssh: SSH.System = SSH.Local,
    build_options: List[Options.Spec] = Nil,
    build_id: String = "",
    isabelle_home: Path = Path.current,
    dirs: List[Path] = Nil,
    quiet: Boolean = false,
    verbose: Boolean = false
  ): String = {
    val options = build_options ::: Options.Spec.eq("build_hostname", host.name) :: host.options
    ssh.bash_path(Isabelle_Tool.exe(isabelle_home)) + " build_worker" +
      if_proper(build_id, " -B " + Bash.string(build_id)) +
      dirs.map(dir => " -d " + ssh.bash_path(dir)).mkString +
      if_proper(host.numa, " -N") + " -j" + host.jobs +
      Options.Spec.bash_strings(options, bg = true) +
      if_proper(quiet, " -q") +
      if_proper(verbose, " -v")
  }

  def build_worker(
    options: Options,
    build_id: String = "",
    progress: Progress = new Progress,
    dirs: List[Path] = Nil,
    numa_shuffling: Boolean = false,
    max_jobs: Option[Int] = None
  ): Results = {
    val engine = Engine(engine_name(options))
    val store = engine.build_store(options, build_cluster = true)
    val build_options = store.options

    using(store.open_server()) { server =>
      using_optional(store.maybe_open_build_database(server = server)) { build_database =>
        val builds = read_builds(build_database)

        val build_master = find_builds(build_database, build_id, builds.filter(_.active))

        val more_dirs = List(Path.ISABELLE_HOME + Sync.DIRS).filter(Sessions.is_session_dir(_))

        val sessions_structure =
          Sessions.load_structure(build_options, dirs = more_dirs ::: dirs).
            selection(Sessions.Selection(sessions = build_master.sessions))

        val build_deps =
          Sessions.deps(sessions_structure, progress = progress, inlined_files = true).check_errors

        val build_context =
          Context(store, build_deps, engine = engine, hostname = hostname(build_options),
            numa_shuffling = numa_shuffling, build_uuid = build_master.build_uuid,
            build_start = Some(build_master.start), jobs = max_jobs.getOrElse(1))

        engine.run_build_process(build_context, progress, server)
      }
    }
  }

  val isabelle_tool3 = Isabelle_Tool("build_worker", "start worker for session build process",
    Scala_Project.here,
    { args =>
      var build_id = ""
      var numa_shuffling = false
      val dirs = new mutable.ListBuffer[Path]
      var max_jobs: Option[Int] = None
      var options =
        Options.init(specs =
          Options.Spec.ISABELLE_BUILD_OPTIONS ::: List(Options.Spec.make("build_database")))
      var quiet = false
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_worker [OPTIONS]

  Options are:
    -B UUID      existing UUID for build process (default: from database)
    -N           cyclic shuffling of NUMA CPU nodes (performance tuning)
    -d DIR       include session directory
    -j INT       maximum number of parallel jobs (default 1)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -q           quiet mode: no progress
    -v           verbose
""",
        "B:" -> (arg => build_id = arg),
        "N" -> (_ => numa_shuffling = true),
        "d:" -> (arg => dirs += Path.explode(arg)),
        "j:" -> (arg => max_jobs = Some(Value.Nat.parse(arg))),
        "o:" -> (arg => options = options + arg),
        "q" -> (_ => quiet = true),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress =
        if (quiet && verbose) new Verbose_Progress with Progress.Global_Interrupts
        else if (quiet) new Progress with Progress.Global_Interrupts
        else new Console_Progress(verbose = verbose)

      progress.interrupt_handler {
        build_worker(options,
          build_id = build_id,
          progress = progress,
          dirs = dirs.toList,
          numa_shuffling = Host.numa_check(progress, numa_shuffling),
          max_jobs = max_jobs)
      }
    })



  /** "isabelle build_log" **/

  /* theory markup/messages from session database */

  def read_theory(
    theory_context: Export.Theory_Context,
    unicode_symbols: Boolean = false,
    migrate_file: String => String = identity
  ): Option[Document.Snapshot] = {
    def decode(str: String): String = Symbol.output(unicode_symbols, str)

    def read(name: String): Export.Entry = theory_context(name, permissive = true)

    def read_xml(name: String): XML.Body =
      YXML.parse_body(read(name).bytes, recode = decode, cache = theory_context.cache)

    def read_source_file(name: String): Store.Source_File =
      theory_context.session_context.source_file(name)

    for {
      id <- theory_context.document_id()
      (thy_file0, blobs_files0) <- theory_context.files(permissive = true)
    }
    yield {
      val thy_file = migrate_file(thy_file0)

      val blobs =
        blobs_files0.map { case (command_offset, name0) =>
          val node_name = Document.Node.Name(migrate_file(name0))
          val src_path = Path.explode(name0)

          val file = read_source_file(name0)
          val bytes = file.bytes
          val text = decode(bytes.text)
          val chunk = Symbol.Text_Chunk(text)
          val content = Some((file.digest, chunk))

          Command.Blob(command_offset, node_name, src_path, content) ->
            Document.Blobs.Item(bytes, text, chunk, command_offset = command_offset)
        }

      val thy_source = decode(read_source_file(thy_file0).bytes.text)
      val thy_xml = read_xml(Export.MARKUP)
      val blobs_xml =
        for (i <- (1 to blobs.length).toList)
          yield read_xml(Export.MARKUP + i)

      val markups_index = Command.Markup_Index.make(blobs.map(_._1))
      val markups =
        Command.Markups.make(
          for ((index, xml) <- markups_index.zip(thy_xml :: blobs_xml))
          yield index -> Markup_Tree.from_XML(xml))

      val results =
        Command.Results.make(
          for (case elem@XML.Elem(Markup(_, Markup.Serial(i)), _) <- read_xml(Export.MESSAGES))
            yield i -> elem)

      val command =
        Command.unparsed(thy_source, theory_commands = Some(0), id = id,
          node_name = Document.Node.Name(thy_file, theory = theory_context.theory),
          blobs_info = Command.Blobs_Info.make(blobs),
          markups = markups, results = results)

      val doc_blobs = Document.Blobs.make(blobs)

      Document.State.init.snippet(List(command), doc_blobs)
    }
  }


  /* print messages */

  def print_log_check(
    pos: Position.T,
    elem: XML.Elem,
    message_head: List[Regex],
    message_body: List[Regex]
  ): Boolean = {
    def check(filter: List[Regex], make_string: => String): Boolean =
      filter.isEmpty || {
        val s = Protocol_Message.clean_output(make_string)
        filter.forall(r => r.findFirstIn(Protocol_Message.clean_output(s)).nonEmpty)
      }

    check(message_head, Protocol.message_heading(elem, pos)) &&
    check(message_body, Pretty.unformatted_string_of(List(elem)))
  }

  def print_log(
    options: Options,
    sessions: List[String],
    theories: List[String] = Nil,
    message_head: List[Regex] = Nil,
    message_body: List[Regex] = Nil,
    progress: Progress = new Progress,
    margin: Double = Pretty.default_margin,
    breakgain: Double = Pretty.default_breakgain,
    metric: Pretty.Metric = Symbol.Metric,
    unicode_symbols: Boolean = false
  ): Unit = {
    val session = Session.bootstrap(options)
    val store = session.store

    def print(session_name: String): Unit = {
      using(Export.open_session_context0(store, session_name)) { session_context =>
        val result =
          for {
            db <- session_context.session_db()
            theories = store.read_theories(db, session_name)
            errors = store.read_errors(db, session_name)
            info <- store.read_build(db, session_name)
          } yield (theories, errors, info.return_code)
        result match {
          case None => store.error_database(session_name)
          case Some((used_theories, errors, rc)) =>
            theories.filterNot(used_theories.toSet) match {
              case Nil =>
              case bad => error("Unknown theories " + commas_quote(bad))
            }
            val print_theories =
              if (theories.isEmpty) used_theories else used_theories.filter(theories.toSet)

            for (thy <- print_theories) {
              val thy_heading = "\nTheory " + quote(thy) + " (in " + session_name + ")" + ":"

              Build.read_theory(session_context.theory(thy), unicode_symbols = unicode_symbols) match {
                case None => progress.echo(thy_heading + " MISSING")
                case Some(snapshot) =>
                  val messages =
                    Rendering.text_messages(snapshot,
                      filter = msg => progress.verbose || Protocol.is_exported(msg))
                  if (messages.nonEmpty) {
                    val line_document = Line.Document(snapshot.node.source)
                    val buffer = new mutable.ListBuffer[String]
                    for (Text.Info(range, elem) <- messages) {
                      val line = line_document.position(range.start).line1
                      val pos = Position.Line_File(line, snapshot.node_name.node)
                      if (print_log_check(pos, elem, message_head, message_body)) {
                        buffer +=
                          Protocol.message_text(elem, heading = true, pos = pos,
                            margin = margin, breakgain = breakgain, metric = metric)
                      }
                    }
                    if (buffer.nonEmpty) {
                      progress.echo(thy_heading)
                      buffer.foreach(progress.echo(_))
                    }
                  }
              }
            }

            if (errors.nonEmpty) {
              val msg = Symbol.output(unicode_symbols, cat_lines(errors))
              progress.echo("\nBuild errors:\n" + Output.error_message_text(msg))
            }
            if (rc != Process_Result.RC.ok) {
              progress.echo("\n" + Process_Result.RC.print_long(rc))
            }
        }
      }
    }

    val errors = new mutable.ListBuffer[String]
    for (session_name <- sessions) {
      Exn.result(print(session_name)) match {
        case Exn.Res(_) =>
        case Exn.Exn(exn) => errors += Exn.message(exn)
      }
    }
    if (errors.nonEmpty) error(cat_lines(errors.toList))
  }


  /* Isabelle tool wrapper */

  val isabelle_tool4 = Isabelle_Tool("build_log", "print messages from session build database",
    Scala_Project.here,
    { args =>
      /* arguments */

      val message_head = new mutable.ListBuffer[Regex]
      val message_body = new mutable.ListBuffer[Regex]
      var unicode_symbols = false
      val theories = new mutable.ListBuffer[String]
      var margin = Pretty.default_margin
      var options = Options.init()
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_log [OPTIONS] [SESSIONS ...]

  Options are:
    -H REGEX     filter messages by matching against head
    -M REGEX     filter messages by matching against body
    -T NAME      restrict to given theories (multiple options possible)
    -U           output Unicode symbols
    -m MARGIN    margin for pretty printing (default: """ + margin + """)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           print all messages, including information etc.

  Print messages from the session build database of the given sessions,
  without any checks against current sources nor session structure: results
  from old sessions or failed builds can be printed as well.

  Multiple options -H and -M are conjunctive: all given patterns need to
  match. Patterns match any substring, but ^ or $ may be used to match the
  start or end explicitly.
""",
        "H:" -> (arg => message_head += arg.r),
        "M:" -> (arg => message_body += arg.r),
        "T:" -> (arg => theories += arg),
        "U" -> (_ => unicode_symbols = true),
        "m:" -> (arg => margin = Value.Double.parse(arg)),
        "o:" -> (arg => options = options + arg),
        "v" -> (_ => verbose = true))

      val sessions = getopts(args)

      val progress = new Console_Progress(verbose = verbose)

      if (sessions.isEmpty) progress.echo_warning("No sessions to print")
      else {
        print_log(options, sessions, theories = theories.toList, message_head = message_head.toList,
          message_body = message_body.toList, margin = margin, progress = progress,
          unicode_symbols = unicode_symbols)
      }
    })
}
