/*  Title:      Pure/Tools/build.scala
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
    engine: Engine,
    build_deps: isabelle.Sessions.Deps,
    afp_root: Option[Path] = None,
    build_hosts: List[Build_Cluster.Host] = Nil,
    ml_platform: String = Isabelle_System.getenv("ML_PLATFORM"),
    hostname: String = Isabelle_System.hostname(),
    numa_shuffling: Boolean = false,
    build_heap: Boolean = false,
    max_jobs: Int = 1,
    fresh_build: Boolean = false,
    no_build: Boolean = false,
    session_setup: (String, Session) => Unit = (_, _) => (),
    build_uuid: String = UUID.random().toString,
    master: Boolean = false
  ) {
    override def toString: String =
      "Build.Context(build_uuid = " + quote(build_uuid) + if_proper(master, ", master = true") + ")"

    def build_options: Options = store.options

    def sessions_structure: isabelle.Sessions.Structure = build_deps.sessions_structure

    def worker_active: Boolean = max_jobs > 0
  }


  /* results */

  object Results {
    def apply(
      context: Context,
      results: Map[String, Process_Result] = Map.empty,
      other_rc: Int = Process_Result.RC.ok
    ): Results = {
      new Results(context.store, context.build_deps, results, other_rc)
    }
  }

  class Results private(
    val store: Store,
    val deps: Sessions.Deps,
    results: Map[String, Process_Result],
    other_rc: Int
  ) {
    def cache: Term.Cache = store.cache

    def sessions_ok: List[String] =
      (for {
        name <- deps.sessions_structure.build_topological_order.iterator
        result <- results.get(name) if result.ok
      } yield name).toList

    def info(name: String): Sessions.Info = deps.sessions_structure(name)
    def sessions: Set[String] = results.keySet
    def cancelled(name: String): Boolean = !results(name).defined
    def apply(name: String): Process_Result = results(name).strict

    val rc: Int =
      Process_Result.RC.merge(other_rc,
        Process_Result.RC.merge(results.valuesIterator.map(_.strict.rc)))
    def ok: Boolean = rc == Process_Result.RC.ok

    lazy val unfinished: List[String] = sessions.iterator.filterNot(apply(_).ok).toList.sorted

    override def toString: String = rc.toString
  }


  /* engine */

  object Engine {
    lazy val services: List[Engine] =
      Isabelle_System.make_services(classOf[Engine])

    def apply(name: String): Engine =
      services.find(_.name == name).getOrElse(error("Bad build engine " + quote(name)))
  }

  class Engine(val name: String) extends Isabelle_System.Service {
    override def toString: String = name

    def build_options(options: Options, build_hosts: List[Build_Cluster.Host] = Nil): Options = {
      val options1 = options + "completion_limit=0" + "editor_tracing_messages=0"
      if (build_hosts.isEmpty) options1
      else options1 + "build_database_server" + "build_database"
    }

    def process_options(options: Options, node_info: Host.Node_Info): Options =
      Host.process_policy_options(options, node_info.numa_node)

    final def build_store(options: Options,
      build_hosts: List[Build_Cluster.Host] = Nil,
      cache: Term.Cache = Term.Cache.make()
    ): Store = {
      val store = Store(build_options(options, build_hosts = build_hosts), cache = cache)
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
        using(open_build_process(context, progress, server))(_.run())
      }
    }
  }

  class Default_Engine extends Engine("") { override def toString: String = "<default>" }


  /* build */

  def build(
    options: Options,
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
    max_jobs: Int = 1,
    list_files: Boolean = false,
    check_keywords: Set[String] = Set.empty,
    fresh_build: Boolean = false,
    no_build: Boolean = false,
    soft_build: Boolean = false,
    export_files: Boolean = false,
    augment_options: String => List[Options.Spec] = _ => Nil,
    session_setup: (String, Session) => Unit = (_, _) => (),
    cache: Term.Cache = Term.Cache.make()
  ): Results = {
    val build_engine = Engine(engine_name(options))

    val store = build_engine.build_store(options, build_hosts = build_hosts, cache = cache)
    val build_options = store.options

    using(store.open_server()) { server =>
      using_optional(store.maybe_open_database_server(server = server)) { database_server =>


        /* session selection and dependencies */

        val full_sessions =
          Sessions.load_structure(build_options, dirs = AFP.make_dirs(afp_root) ::: dirs,
            select_dirs = select_dirs, infos = infos, augment_options = augment_options)
        val full_sessions_selection = full_sessions.imports_selection(selection)

        val build_deps = {
          val deps0 =
            Sessions.deps(full_sessions.selection(selection), progress = progress, inlined_files = true,
              list_files = list_files, check_keywords = check_keywords).check_errors

          if (soft_build && !fresh_build) {
            val outdated =
              deps0.sessions_structure.build_topological_order.flatMap(name =>
                store.try_open_database(name, server = server) match {
                  case Some(db) =>
                    using(db)(store.read_build(_, name)) match {
                      case Some(build) if build.ok =>
                        val session_options = deps0.sessions_structure(name).options
                        val session_sources = deps0.sources_shasum(name)
                        if (Sessions.eq_sources(session_options, build.sources, session_sources)) None
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
            (for {
              (_, base) <- build_deps.session_bases.iterator
              (path, _) <- base.session_sources.iterator
            } yield path).toList
          Mercurial.check_files(source_files)._2 match {
            case Nil =>
            case unknown_files =>
              progress.echo_warning("Unknown files (not part of the underlying Mercurial repository):" +
                unknown_files.map(File.standard_path).sorted.mkString("\n  ", "\n  ", ""))
          }
        }


        /* build process and results */

        val build_context =
          Context(store, build_engine, build_deps, afp_root = afp_root, build_hosts = build_hosts,
            hostname = hostname(build_options), build_heap = build_heap,
            numa_shuffling = numa_shuffling, max_jobs = max_jobs, fresh_build = fresh_build,
            no_build = no_build, session_setup = session_setup, master = true)

        if (clean_build) {
          for (name <- full_sessions.imports_descendants(full_sessions_selection)) {
            store.clean_output(database_server, name) match {
              case None =>
              case Some(true) => progress.echo("Cleaned " + name)
              case Some(false) => progress.echo(name + " FAILED to clean")
            }
          }
        }

        val results = build_engine.run_build_process(build_context, progress, server)

        if (export_files) {
          for (name <- full_sessions_selection.iterator if results(name).ok) {
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
  }


  /* build logic image */

  def build_logic(options: Options, logic: String,
    progress: Progress = new Progress,
    build_heap: Boolean = false,
    dirs: List[Path] = Nil,
    fresh: Boolean = false,
    strict: Boolean = false
  ): Int = {
    val selection = Sessions.Selection.session(logic)
    val rc =
      if (!fresh && build(options, selection = selection,
            build_heap = build_heap, no_build = true, dirs = dirs).ok) Process_Result.RC.ok
      else {
        progress.echo("Build started for Isabelle/" + logic + " ...")
        build(options, selection = selection, progress = progress,
          build_heap = build_heap, fresh_build = fresh, dirs = dirs).rc
      }
    if (strict && rc != Process_Result.RC.ok) error("Failed to build Isabelle/" + logic) else rc
  }


  /* command-line wrapper */

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
      var max_jobs = 1
      var check_keywords: Set[String] = Set.empty
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
    -H HOSTS     additional build cluster host specifications, of the form
                 "NAMES:PARAMETERS" (separated by commas)
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
    -j INT       maximum number of parallel jobs (default 1)
    -k KEYWORD   check theory sources for conflicts with proposed keywords
    -l           list session source files
    -n           no build -- take existing session build databases
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Build and manage Isabelle sessions: ML heaps, session databases, documents.

  Parameters for host specifications (option -H), apart from system options:
""" + Library.indent_lines(4, Build_Cluster.Host.parameters.print()) +
"""

  Notable system options: see "isabelle options -l -t build"

  Notable system settings:
""" + Library.indent_lines(4, Build_Log.Settings.show()) + "\n",
        "A:" -> (arg => afp_root = Some(if (arg == ":") AFP.BASE else Path.explode(arg))),
        "B:" -> (arg => base_sessions += arg),
        "D:" -> (arg => select_dirs += Path.explode(arg)),
        "H:" -> (arg => build_hosts ++= Build_Cluster.Host.parse(arg)),
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
        "j:" -> (arg => max_jobs = Value.Int.parse(arg)),
        "k:" -> (arg => check_keywords = check_keywords + arg),
        "l" -> (_ => list_files = true),
        "n" -> (_ => no_build = true),
        "o:" -> (arg => options = options + arg),
        "v" -> (_ => verbose = true),
        "x:" -> (arg => exclude_sessions += arg))

      val sessions = getopts(args)

      val progress = new Console_Progress(verbose = verbose)

      val start_date = Date.now()

      progress.echo(
        "Started at " + Build_Log.print_date(start_date) +
          " (" + Isabelle_System.ml_identifier() + " on " + hostname(options) +")",
        verbose = true)
      progress.echo(Build_Log.Settings.show() + "\n", verbose = true)

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
            check_keywords = check_keywords,
            fresh_build = fresh_build,
            no_build = no_build,
            soft_build = soft_build,
            export_files = export_files,
            build_hosts = build_hosts.toList)
        }
      val stop_date = Date.now()
      val elapsed_time = stop_date.time - start_date.time

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
    list_builds: Boolean = false,
    remove_builds: Boolean = false,
    force: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    val build_engine = Engine(engine_name(options))
    val store = build_engine.build_store(options)

    using(store.open_server()) { server =>
      using_optional(store.maybe_open_build_database(server = server)) { build_database =>
        def print(builds: List[Build_Process.Build]): Unit =
          if (list_builds) progress.echo(print_builds(build_database, builds))

        build_database match {
          case None => print(Nil)
          case Some(db) =>
            Build_Process.private_data.transaction_lock(db, create = true, label = "build_process") {
              val builds = Build_Process.private_data.read_builds(db)
              val remove =
                if (!remove_builds) Nil
                else if (force) builds.map(_.build_uuid)
                else builds.flatMap(build => if (build.active) None else Some(build.build_uuid))

              print(builds)
              if (remove.nonEmpty) {
                if (remove_builds) {
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
      var force = false
      var list_builds = false
      var options =
        Options.init(specs = Options.Spec.ISABELLE_BUILD_OPTIONS :::
          List(
            Options.Spec.make("build_database_server"),
            Options.Spec.make("build_database")))
      var remove_builds = false

      val getopts = Getopts("""
Usage: isabelle build_process [OPTIONS]

  Options are:
    -f           extra force for option -r
    -l           list build processes
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -r           remove data from build processes: inactive processes (default)
                 or all processes (option -f)
""",
        "f" -> (_ => force = true),
        "l" -> (_ => list_builds = true),
        "o:" -> (arg => options = options + arg),
        "r" -> (_ => remove_builds = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      build_process(options, list_builds = list_builds, remove_builds = remove_builds,
        force = force, progress = progress)
    })



  /* "isabelle build_worker" */

  def build_worker_command(
    host: Build_Cluster.Host,
    ssh: SSH.System = SSH.Local,
    build_options: List[Options.Spec] = Nil,
    build_id: String = "",
    isabelle_home: Path = Path.current,
    afp_root: Option[Path] = None,
    dirs: List[Path] = Nil,
    quiet: Boolean = false,
    verbose: Boolean = false
  ): String = {
    val options =
      build_options ::: Options.Spec("build_hostname", Some(host.name)) :: host.options
    ssh.bash_path(isabelle_home + Path.explode("bin/isabelle")) + " build_worker" +
      if_proper(build_id, " -B " + Bash.string(build_id)) +
      if_proper(afp_root, " -A " + ssh.bash_path(afp_root.get)) +
      dirs.map(dir => " -d " + ssh.bash_path(dir)).mkString +
      if_proper(host.numa, " -N") + " -j" + host.jobs +
      options.map(opt => " -o " + Bash.string(opt.print)).mkString +
      if_proper(quiet, " -q") +
      if_proper(verbose, " -v")
  }

  def build_worker(
    options: Options,
    build_id: String = "",
    progress: Progress = new Progress,
    afp_root: Option[Path] = None,
    dirs: List[Path] = Nil,
    numa_shuffling: Boolean = false,
    max_jobs: Int = 1
  ): Results = {
    val build_engine = Engine(engine_name(options))
    val store = build_engine.build_store(options)
    val build_options = store.options

    using(store.open_server()) { server =>
      using_optional(store.maybe_open_build_database(server = server)) { build_database =>
        val builds = read_builds(build_database)

        val build_master = find_builds(build_database, build_id, builds.filter(_.active))

        val sessions_structure =
          Sessions.load_structure(build_options, dirs = AFP.make_dirs(afp_root) ::: dirs).
            selection(Sessions.Selection(sessions = build_master.sessions))

        val build_deps =
          Sessions.deps(sessions_structure, progress = progress, inlined_files = true).check_errors

        val build_context =
          Context(store, build_engine, build_deps, afp_root = afp_root,
            hostname = hostname(build_options), numa_shuffling = numa_shuffling,
            max_jobs = max_jobs, build_uuid = build_master.build_uuid)

        build_engine.run_build_process(build_context, progress, server)
      }
    }
  }

  val isabelle_tool3 = Isabelle_Tool("build_worker", "start worker for session build process",
    Scala_Project.here,
    { args =>
      var afp_root: Option[Path] = None
      var build_id = ""
      var numa_shuffling = false
      val dirs = new mutable.ListBuffer[Path]
      var max_jobs = 1
      var options =
        Options.init(specs = Options.Spec.ISABELLE_BUILD_OPTIONS :::
          List(
            Options.Spec.make("build_database_server"),
            Options.Spec.make("build_database")))
      var quiet = false
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_worker [OPTIONS]

  Options are:
    -A ROOT      include AFP with given root directory (":" for """ + AFP.BASE.implode + """)
    -B UUID      existing UUID for build process (default: from database)
    -N           cyclic shuffling of NUMA CPU nodes (performance tuning)
    -d DIR       include session directory
    -j INT       maximum number of parallel jobs (default 1)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -q           quiet mode: no progress
    -v           verbose
""",
        "A:" -> (arg => afp_root = Some(if (arg == ":") AFP.BASE else Path.explode(arg))),
        "B:" -> (arg => build_id = arg),
        "N" -> (_ => numa_shuffling = true),
        "d:" -> (arg => dirs += Path.explode(arg)),
        "j:" -> (arg => max_jobs = Value.Int.parse(arg)),
        "o:" -> (arg => options = options + arg),
        "q" -> (_ => quiet = true),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress =
        if (quiet && verbose) new Progress { override def verbose: Boolean = true }
        else if (quiet) new Progress
        else new Console_Progress(verbose = verbose)

      val results =
        progress.interrupt_handler {
          build_worker(options,
            build_id = build_id,
            progress = progress,
            afp_root = afp_root,
            dirs = dirs.toList,
            numa_shuffling = Host.numa_check(progress, numa_shuffling),
            max_jobs = max_jobs)
        }

      if (!results.ok) sys.exit(results.rc)
    })



  /** "isabelle build_log" **/

  /* theory markup/messages from session database */

  def read_theory(
    theory_context: Export.Theory_Context,
    unicode_symbols: Boolean = false
  ): Option[Document.Snapshot] = {
    def decode_bytes(bytes: Bytes): String =
      Symbol.output(unicode_symbols, UTF8.decode_permissive(bytes))

    def read(name: String): Export.Entry = theory_context(name, permissive = true)

    def read_xml(name: String): XML.Body =
      YXML.parse_body(decode_bytes(read(name).bytes), cache = theory_context.cache)

    def read_source_file(name: String): Store.Source_File =
      theory_context.session_context.source_file(name)

    for {
      id <- theory_context.document_id()
      (thy_file, blobs_files) <- theory_context.files(permissive = true)
    }
    yield {
      val master_dir =
        Path.explode(Url.strip_base_name(thy_file).getOrElse(
          error("Cannot determine theory master directory: " + quote(thy_file))))

      val blobs =
        blobs_files.map { name =>
          val path = Path.explode(name)
          val src_path = File.relative_path(master_dir, path).getOrElse(path)

          val file = read_source_file(name)
          val bytes = file.bytes
          val text = decode_bytes(bytes)
          val chunk = Symbol.Text_Chunk(text)

          Command.Blob(Document.Node.Name(name), src_path, Some((file.digest, chunk))) ->
            Document.Blobs.Item(bytes, text, chunk, changed = false)
        }

      val thy_source = decode_bytes(read_source_file(thy_file).bytes)
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
        Command.unparsed(thy_source, theory = true, id = id,
          node_name = Document.Node.Name(thy_file, theory = theory_context.theory),
          blobs_info = Command.Blobs_Info.make(blobs),
          markups = markups, results = results)

      val doc_blobs = Document.Blobs.make(blobs)

      Document.State.init.snippet(command, doc_blobs)
    }
  }


  /* print messages */

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
    val store = Store(options)
    val session = new Session(options, Resources.bootstrap)

    def check(filter: List[Regex], make_string: => String): Boolean =
      filter.isEmpty || {
        val s = Output.clean_yxml(make_string)
        filter.forall(r => r.findFirstIn(Output.clean_yxml(s)).nonEmpty)
      }

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
                  val rendering = new Rendering(snapshot, options, session)
                  val messages =
                    rendering.text_messages(Text.Range.full)
                      .filter(message => progress.verbose || Protocol.is_exported(message.info))
                  if (messages.nonEmpty) {
                    val line_document = Line.Document(snapshot.node.source)
                    val buffer = new mutable.ListBuffer[String]
                    for (Text.Info(range, elem) <- messages) {
                      val line = line_document.position(range.start).line1
                      val pos = Position.Line_File(line, snapshot.node_name.node)
                      def message_text: String =
                        Protocol.message_text(elem, heading = true, pos = pos,
                          margin = margin, breakgain = breakgain, metric = metric)
                      val ok =
                        check(message_head, Protocol.message_heading(elem, pos)) &&
                        check(message_body, XML.content(Pretty.unformatted(List(elem))))
                      if (ok) buffer += message_text
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


  /* command-line wrapper */

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
