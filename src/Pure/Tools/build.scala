/*  Title:      Pure/Tools/build.scala
    Author:     Makarius
    Options:    :folding=explicit:

Build and manage Isabelle sessions.
*/

package isabelle


object Build {
  /** build with results **/

  class Results private[Build](
    val store: Sessions.Store,
    val deps: Sessions.Deps,
    val sessions_ok: List[String],
    results: Map[String, Process_Result]
  ) {
    def cache: Term.Cache = store.cache

    def info(name: String): Sessions.Info = deps.sessions_structure(name)
    def sessions: Set[String] = results.keySet
    def cancelled(name: String): Boolean = !results(name).defined
    def apply(name: String): Process_Result = results(name).strict
    val rc: Int = results.valuesIterator.map(_.strict.rc).foldLeft(Process_Result.RC.ok)(_ max _)
    def ok: Boolean = rc == Process_Result.RC.ok

    def unfinished: List[String] = sessions.iterator.filterNot(apply(_).ok).toList.sorted

    override def toString: String = rc.toString
  }

  def build(
    options: Options,
    selection: Sessions.Selection = Sessions.Selection.empty,
    browser_info: Browser_Info.Config = Browser_Info.Config.none,
    progress: Progress = new Progress,
    check_unknown_files: Boolean = false,
    build_heap: Boolean = false,
    clean_build: Boolean = false,
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
    verbose: Boolean = false,
    export_files: Boolean = false,
    augment_options: String => List[Options.Spec] = _ => Nil,
    session_setup: (String, Session) => Unit = (_, _) => ()
  ): Results = {
    val build_options =
      options +
        "completion_limit=0" +
        "editor_tracing_messages=0" +
        ("pide_reports=" + options.bool("build_pide_reports"))

    val store = Sessions.store(build_options)

    Isabelle_Fonts.init()


    /* session selection and dependencies */

    val full_sessions =
      Sessions.load_structure(build_options, dirs = dirs, select_dirs = select_dirs, infos = infos,
        augment_options = augment_options)
    val full_sessions_selection = full_sessions.imports_selection(selection)

    val build_deps = {
      val deps0 =
        Sessions.deps(full_sessions.selection(selection),
          progress = progress, inlined_files = true, verbose = verbose,
          list_files = list_files, check_keywords = check_keywords).check_errors

      if (soft_build && !fresh_build) {
        val outdated =
          deps0.sessions_structure.build_topological_order.flatMap(name =>
            store.try_open_database(name) match {
              case Some(db) =>
                using(db)(store.read_build(_, name)) match {
                  case Some(build)
                  if build.ok && build.sources == deps0.sources_shasum(name) => None
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

    val build_context = Build_Process.Context(store, build_deps, progress = progress)

    store.prepare_output_dir()

    if (clean_build) {
      for (name <- full_sessions.imports_descendants(full_sessions_selection)) {
        val (relevant, ok) = store.clean_output(name)
        if (relevant) {
          if (ok) progress.echo("Cleaned " + name)
          else progress.echo(name + " FAILED to clean")
        }
      }
    }

    val results = {
      val process_results =
        Isabelle_Thread.uninterruptible {
          val build_process =
            new Build_Process(build_context, build_heap = build_heap,
              numa_shuffling = numa_shuffling, max_jobs = max_jobs, fresh_build = fresh_build,
              no_build = no_build, verbose = verbose, session_setup = session_setup)
          build_process.run()
        }

      val sessions_ok: List[String] =
        (for {
          name <- build_deps.sessions_structure.build_topological_order.iterator
          result <- process_results.get(name)
          if result.ok
        } yield name).toList

      new Results(store, build_deps, sessions_ok, process_results)
    }

    if (export_files) {
      for (name <- full_sessions_selection.iterator if results(name).ok) {
        val info = results.info(name)
        if (info.export_files.nonEmpty) {
          progress.echo("Exporting " + info.name + " ...")
          for ((dir, prune, pats) <- info.export_files) {
            Export.export_files(store, name, info.dir + dir,
              progress = if (verbose) progress else new Progress,
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
        progress = progress, verbose = verbose)
    }

    if (!results.ok && (verbose || !no_build)) {
      progress.echo("Unfinished session(s): " + commas(results.unfinished))
    }

    results
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("build", "build and manage Isabelle sessions",
    Scala_Project.here,
    { args =>
      val build_options = Word.explode(Isabelle_System.getenv("ISABELLE_BUILD_OPTIONS"))

      var base_sessions: List[String] = Nil
      var select_dirs: List[Path] = Nil
      var numa_shuffling = false
      var browser_info = Browser_Info.Config.none
      var requirements = false
      var soft_build = false
      var exclude_session_groups: List[String] = Nil
      var all_sessions = false
      var build_heap = false
      var clean_build = false
      var dirs: List[Path] = Nil
      var export_files = false
      var fresh_build = false
      var session_groups: List[String] = Nil
      var max_jobs = 1
      var check_keywords: Set[String] = Set.empty
      var list_files = false
      var no_build = false
      var options = Options.init(opts = build_options)
      var verbose = false
      var exclude_sessions: List[String] = Nil

      val getopts = Getopts("""
Usage: isabelle build [OPTIONS] [SESSIONS ...]

  Options are:
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
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
    -n           no build -- take existing build databases
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Build and manage Isabelle sessions, depending on implicit settings:

""" + Library.indent_lines(2,  Build_Log.Settings.show()) + "\n",
        "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
        "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
        "N" -> (_ => numa_shuffling = true),
        "P:" -> (arg => browser_info = Browser_Info.Config.make(arg)),
        "R" -> (_ => requirements = true),
        "S" -> (_ => soft_build = true),
        "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
        "a" -> (_ => all_sessions = true),
        "b" -> (_ => build_heap = true),
        "c" -> (_ => clean_build = true),
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
        "e" -> (_ => export_files = true),
        "f" -> (_ => fresh_build = true),
        "g:" -> (arg => session_groups = session_groups ::: List(arg)),
        "j:" -> (arg => max_jobs = Value.Int.parse(arg)),
        "k:" -> (arg => check_keywords = check_keywords + arg),
        "l" -> (_ => list_files = true),
        "n" -> (_ => no_build = true),
        "o:" -> (arg => options = options + arg),
        "v" -> (_ => verbose = true),
        "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

      val sessions = getopts(args)

      val progress = new Console_Progress(verbose = verbose)

      val start_date = Date.now()

      if (verbose) {
        progress.echo(
          "Started at " + Build_Log.print_date(start_date) +
            " (" + Isabelle_System.getenv("ML_IDENTIFIER") + " on " + Isabelle_System.hostname() +")")
        progress.echo(Build_Log.Settings.show() + "\n")
      }

      val results =
        progress.interrupt_handler {
          build(options,
            selection = Sessions.Selection(
              requirements = requirements,
              all_sessions = all_sessions,
              base_sessions = base_sessions,
              exclude_session_groups = exclude_session_groups,
              exclude_sessions = exclude_sessions,
              session_groups = session_groups,
              sessions = sessions),
            browser_info = browser_info,
            progress = progress,
            check_unknown_files = Mercurial.is_repository(Path.ISABELLE_HOME),
            build_heap = build_heap,
            clean_build = clean_build,
            dirs = dirs,
            select_dirs = select_dirs,
            numa_shuffling = NUMA.enabled_warning(progress, numa_shuffling),
            max_jobs = max_jobs,
            list_files = list_files,
            check_keywords = check_keywords,
            fresh_build = fresh_build,
            no_build = no_build,
            soft_build = soft_build,
            verbose = verbose,
            export_files = export_files)
        }
      val end_date = Date.now()
      val elapsed_time = end_date.time - start_date.time

      if (verbose) {
        progress.echo("\nFinished at " + Build_Log.print_date(end_date))
      }

      val total_timing =
        results.sessions.iterator.map(a => results(a).timing).foldLeft(Timing.zero)(_ + _).
          copy(elapsed = elapsed_time)
      progress.echo(total_timing.message_resources)

      sys.exit(results.rc)
    })


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
        Build.build(options, selection = selection, progress = progress,
          build_heap = build_heap, fresh_build = fresh, dirs = dirs).rc
      }
    if (strict && rc != Process_Result.RC.ok) error("Failed to build Isabelle/" + logic) else rc
  }
}
