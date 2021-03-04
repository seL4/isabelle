/*  Title:      Pure/Tools/build.scala
    Author:     Makarius
    Options:    :folding=explicit:

Build and manage Isabelle sessions.
*/

package isabelle


import scala.collection.SortedSet
import scala.annotation.tailrec


object Build
{
  /** auxiliary **/

  /* persistent build info */

  sealed case class Session_Info(
    sources: String,
    input_heaps: List[String],
    output_heap: Option[String],
    return_code: Int)
  {
    def ok: Boolean = return_code == 0
  }


  /* queue with scheduling information */

  private object Queue
  {
    type Timings = (List[Properties.T], Double)

    def load_timings(progress: Progress, store: Sessions.Store, session_name: String): Timings =
    {
      val no_timings: Timings = (Nil, 0.0)

      store.try_open_database(session_name) match {
        case None => no_timings
        case Some(db) =>
          def ignore_error(msg: String) =
          {
            progress.echo_warning("Ignoring bad database " + db + (if (msg == "") "" else "\n" + msg))
            no_timings
          }
          try {
            val command_timings = store.read_command_timings(db, session_name)
            val session_timing =
              store.read_session_timing(db, session_name) match {
                case Markup.Elapsed(t) => t
                case _ => 0.0
              }
            (command_timings, session_timing)
          }
          catch {
            case ERROR(msg) => ignore_error(msg)
            case exn: java.lang.Error => ignore_error(Exn.message(exn))
            case _: XML.Error => ignore_error("")
          }
          finally { db.close }
      }
    }

    def make_session_timing(sessions_structure: Sessions.Structure, timing: Map[String, Double])
      : Map[String, Double] =
    {
      val maximals = sessions_structure.build_graph.maximals.toSet
      def desc_timing(session_name: String): Double =
      {
        if (maximals.contains(session_name)) timing(session_name)
        else {
          val descendants = sessions_structure.build_descendants(List(session_name)).toSet
          val g = sessions_structure.build_graph.restrict(descendants)
          (0.0 :: g.maximals.flatMap(desc => {
            val ps = g.all_preds(List(desc))
            if (ps.exists(p => !timing.isDefinedAt(p))) None
            else Some(ps.map(timing(_)).sum)
          })).max
        }
      }
      timing.keySet.iterator.map(name => (name -> desc_timing(name))).toMap.withDefaultValue(0.0)
    }

    def apply(progress: Progress, sessions_structure: Sessions.Structure, store: Sessions.Store)
      : Queue =
    {
      val graph = sessions_structure.build_graph
      val names = graph.keys

      val timings = names.map(name => (name, load_timings(progress, store, name)))
      val command_timings =
        timings.map({ case (name, (ts, _)) => (name, ts) }).toMap.withDefaultValue(Nil)
      val session_timing =
        make_session_timing(sessions_structure,
          timings.map({ case (name, (_, t)) => (name, t) }).toMap)

      object Ordering extends scala.math.Ordering[String]
      {
        def compare_timing(name1: String, name2: String): Int =
        {
          val t1 = session_timing(name1)
          val t2 = session_timing(name2)
          if (t1 == 0.0 || t2 == 0.0) 0
          else t1 compare t2
        }

        def compare(name1: String, name2: String): Int =
          compare_timing(name2, name1) match {
            case 0 =>
              sessions_structure(name2).timeout compare sessions_structure(name1).timeout match {
                case 0 => name1 compare name2
                case ord => ord
              }
            case ord => ord
          }
      }

      new Queue(graph, SortedSet(names: _*)(Ordering), command_timings)
    }
  }

  private class Queue(
    graph: Graph[String, Sessions.Info],
    order: SortedSet[String],
    val command_timings: String => List[Properties.T])
  {
    def is_inner(name: String): Boolean = !graph.is_maximal(name)

    def is_empty: Boolean = graph.is_empty

    def - (name: String): Queue =
      new Queue(graph.del_node(name),
        order - name,  // FIXME scala-2.10.0 .. 2.12.4 TreeSet problem!?
        command_timings)

    def dequeue(skip: String => Boolean): Option[(String, Sessions.Info)] =
    {
      val it = order.iterator.dropWhile(name =>
        skip(name)
          || !graph.defined(name)  // FIXME scala-2.10.0 .. 2.12.4 TreeSet problem!?
          || !graph.is_minimal(name))
      if (it.hasNext) { val name = it.next(); Some((name, graph.get_node(name))) }
      else None
    }
  }



  /** build with results **/

  class Results private[Build](results: Map[String, (Option[Process_Result], Sessions.Info)])
  {
    def sessions: Set[String] = results.keySet
    def infos: List[Sessions.Info] = results.values.map(_._2).toList
    def cancelled(name: String): Boolean = results(name)._1.isEmpty
    def apply(name: String): Process_Result = results(name)._1.getOrElse(Process_Result(1))
    def info(name: String): Sessions.Info = results(name)._2
    val rc: Int =
      results.iterator.map({ case (_, (Some(r), _)) => r.rc case (_, (None, _)) => 1 }).
        foldLeft(0)(_ max _)
    def ok: Boolean = rc == 0

    override def toString: String = rc.toString
  }

  def session_finished(session_name: String, process_result: Process_Result): String =
    "Finished " + session_name + " (" + process_result.timing.message_resources + ")"

  def session_timing(session_name: String, build_log: Build_Log.Session_Info): String =
  {
    val props = build_log.session_timing
    val threads = Markup.Session_Timing.Threads.unapply(props) getOrElse 1
    val timing = Markup.Timing_Properties.parse(props)
    "Timing " + session_name + " (" + threads + " threads, " + timing.message_factor + ")"
  }

  def build(
    options: Options,
    selection: Sessions.Selection = Sessions.Selection.empty,
    presentation: Presentation.Context = Presentation.Context.none,
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
    export_files: Boolean = false): Results =
  {
    val build_options =
      options +
        "completion_limit=0" +
        "editor_tracing_messages=0" +
        "kodkod_scala=false" +
        ("pide_reports=" + options.bool("build_pide_reports"))

    val store = Sessions.store(build_options)

    Isabelle_Fonts.init()


    /* session selection and dependencies */

    val full_sessions =
      Sessions.load_structure(build_options, dirs = dirs, select_dirs = select_dirs, infos = infos)

    val full_sessions_selection = full_sessions.imports_selection(selection)

    def sources_stamp(deps: Sessions.Deps, session_name: String): String =
    {
      val digests =
        full_sessions(session_name).meta_digest ::
        deps.sources(session_name) :::
        deps.imported_sources(session_name)
      SHA1.digest_set(digests).toString
    }

    val deps =
    {
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
                  if build.ok && build.sources == sources_stamp(deps0, name) => None
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
          (_, base) <- deps.session_bases.iterator
          (path, _) <- base.sources.iterator
        } yield path).toList
      val exclude_files = List(Path.explode("$POLYML_EXE")).map(_.canonical_file)
      val unknown_files =
        Mercurial.check_files(source_files)._2.
          filterNot(path => exclude_files.contains(path.canonical_file))
      if (unknown_files.nonEmpty) {
        progress.echo_warning("Unknown files (not part of the underlying Mercurial repository):" +
          unknown_files.map(path => path.expand.implode).sorted.mkString("\n  ", "\n  ", ""))
      }
    }


    /* main build process */

    val queue = Queue(progress, deps.sessions_structure, store)

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

    // scheduler loop
    case class Result(
      current: Boolean,
      heap_digest: Option[String],
      process: Option[Process_Result],
      info: Sessions.Info)
    {
      def ok: Boolean =
        process match {
          case None => false
          case Some(res) => res.rc == 0
        }
    }

    def sleep(): Unit =
      Isabelle_Thread.interrupt_handler(_ => progress.stop) { Time.seconds(0.5).sleep }

    val numa_nodes = new NUMA.Nodes(numa_shuffling)

    @tailrec def loop(
      pending: Queue,
      running: Map[String, (List[String], Build_Job)],
      results: Map[String, Result]): Map[String, Result] =
    {
      def used_node(i: Int): Boolean =
        running.iterator.exists(
          { case (_, (_, job)) => job.numa_node.isDefined && job.numa_node.get == i })

      if (pending.is_empty) results
      else {
        if (progress.stopped) {
          for ((_, (_, job)) <- running) job.terminate
        }

        running.find({ case (_, (_, job)) => job.is_finished }) match {
          case Some((session_name, (input_heaps, job))) =>
            //{{{ finish job

            val (process_result, heap_digest) = job.join

            val log_lines = process_result.out_lines.filterNot(Protocol_Message.Marker.test)
            val process_result_tail =
            {
              val tail = job.info.options.int("process_output_tail")
              process_result.copy(
                out_lines =
                  "(see also " + store.output_log(session_name).file.toString + ")" ::
                  (if (tail == 0) log_lines else log_lines.drop(log_lines.length - tail max 0)))
            }

            val build_log =
              Build_Log.Log_File(session_name, process_result.out_lines).
                parse_session_info(
                  command_timings = true,
                  theory_timings = true,
                  ml_statistics = true,
                  task_statistics = true)

            // write log file
            if (process_result.ok) {
              File.write_gzip(store.output_log_gz(session_name), terminate_lines(log_lines))
            }
            else File.write(store.output_log(session_name), terminate_lines(log_lines))

            // write database
            using(store.open_database(session_name, output = true))(db =>
              store.write_session_info(db, session_name,
                build_log =
                  if (process_result.timeout) build_log.error("Timeout") else build_log,
                build =
                  Session_Info(sources_stamp(deps, session_name), input_heaps, heap_digest,
                    process_result.rc)))

            // messages
            process_result.err_lines.foreach(progress.echo)

            if (process_result.ok) {
              if (verbose) progress.echo(session_timing(session_name, build_log))
              progress.echo(session_finished(session_name, process_result))
            }
            else {
              progress.echo(session_name + " FAILED")
              if (!process_result.interrupted) progress.echo(process_result_tail.out)
            }

            loop(pending - session_name, running - session_name,
              results +
                (session_name -> Result(false, heap_digest, Some(process_result_tail), job.info)))
            //}}}
          case None if running.size < (max_jobs max 1) =>
            //{{{ check/start next job
            pending.dequeue(running.isDefinedAt) match {
              case Some((session_name, info)) =>
                val ancestor_results =
                  deps.sessions_structure.build_requirements(List(session_name)).
                    filterNot(_ == session_name).map(results(_))
                val ancestor_heaps = ancestor_results.flatMap(_.heap_digest)

                val do_store =
                  build_heap || Sessions.is_pure(session_name) || queue.is_inner(session_name)

                val (current, heap_digest) =
                {
                  store.try_open_database(session_name) match {
                    case Some(db) =>
                      using(db)(store.read_build(_, session_name)) match {
                        case Some(build) =>
                          val heap_digest = store.find_heap_digest(session_name)
                          val current =
                            !fresh_build &&
                            build.ok &&
                            build.sources == sources_stamp(deps, session_name) &&
                            build.input_heaps == ancestor_heaps &&
                            build.output_heap == heap_digest &&
                            !(do_store && heap_digest.isEmpty)
                          (current, heap_digest)
                        case None => (false, None)
                      }
                    case None => (false, None)
                  }
                }
                val all_current = current && ancestor_results.forall(_.current)

                if (all_current)
                  loop(pending - session_name, running,
                    results +
                      (session_name -> Result(true, heap_digest, Some(Process_Result(0)), info)))
                else if (no_build) {
                  progress.echo_if(verbose, "Skipping " + session_name + " ...")
                  loop(pending - session_name, running,
                    results +
                      (session_name -> Result(false, heap_digest, Some(Process_Result(1)), info)))
                }
                else if (ancestor_results.forall(_.ok) && !progress.stopped) {
                  progress.echo((if (do_store) "Building " else "Running ") + session_name + " ...")

                  store.clean_output(session_name)
                  using(store.open_database(session_name, output = true))(
                    store.init_session_info(_, session_name))

                  val numa_node = numa_nodes.next(used_node)
                  val job =
                    new Build_Job(progress, session_name, info, deps, store, do_store,
                      verbose, numa_node, queue.command_timings(session_name))
                  loop(pending, running + (session_name -> (ancestor_heaps, job)), results)
                }
                else {
                  progress.echo(session_name + " CANCELLED")
                  loop(pending - session_name, running,
                    results + (session_name -> Result(false, heap_digest, None, info)))
                }
              case None => sleep(); loop(pending, running, results)
            }
            ///}}}
          case None => sleep(); loop(pending, running, results)
        }
      }
    }


    /* build results */

    val results =
    {
      val results0 =
        if (deps.is_empty) {
          progress.echo_warning("Nothing to build")
          Map.empty[String, Result]
        }
        else Isabelle_Thread.uninterruptible { loop(queue, Map.empty, Map.empty) }

      new Results(
        (for ((name, result) <- results0.iterator)
          yield (name, (result.process, result.info))).toMap)
    }

    if (export_files) {
      for (name <- full_sessions.imports_selection(selection).iterator if results(name).ok) {
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

    if (results.rc != 0 && (verbose || !no_build)) {
      val unfinished =
        (for {
          name <- results.sessions.iterator
          if !results(name).ok
         } yield name).toList.sorted
      progress.echo("Unfinished session(s): " + commas(unfinished))
    }


    /* PDF/HTML presentation */

    if (!no_build && !progress.stopped && results.ok) {
      val selected = full_sessions_selection.toSet
      val presentation_chapters =
        (for {
          session_name <- deps.sessions_structure.build_topological_order.iterator
          info = results.info(session_name)
          if selected(session_name) && presentation.enabled(info) && results(session_name).ok }
        yield (info.chapter, (session_name, info.description))).toList

      if (presentation_chapters.nonEmpty) {
        val presentation_dir = presentation.dir(store)
        progress.echo("Presentation in " + presentation_dir.absolute)

        val resources = Resources.empty
        val html_context = Presentation.html_context()

        using(store.open_database_context())(db_context =>
          for ((_, (session_name, _)) <- presentation_chapters) {
            progress.expose_interrupt()
            progress.echo("Presenting " + session_name + " ...")
            Presentation.session_html(
              resources, session_name, deps, db_context, progress = progress,
              verbose = verbose, html_context = html_context,
              elements = Presentation.elements1, presentation = presentation)
          })

        val browser_chapters =
          presentation_chapters.groupBy(_._1).
            map({ case (chapter, es) => (chapter, es.map(_._2)) }).filterNot(_._2.isEmpty)

        for ((chapter, entries) <- browser_chapters)
          Presentation.update_chapter_index(presentation_dir, chapter, entries)

        if (browser_chapters.nonEmpty) Presentation.make_global_index(presentation_dir)
      }
    }

    results
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("build", "build and manage Isabelle sessions",
    Scala_Project.here, args =>
  {
    val build_options = Word.explode(Isabelle_System.getenv("ISABELLE_BUILD_OPTIONS"))

    var base_sessions: List[String] = Nil
    var select_dirs: List[Path] = Nil
    var numa_shuffling = false
    var presentation = Presentation.Context.none
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
    -n           no build -- test dependencies only
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Build and manage Isabelle sessions, depending on implicit settings:

""" + Library.prefix_lines("  ",  Build_Log.Settings.show()) + "\n",
      "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
      "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
      "N" -> (_ => numa_shuffling = true),
      "P:" -> (arg => presentation = Presentation.Context.make(arg)),
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
          presentation = presentation,
          progress = progress,
          check_unknown_files = Mercurial.is_repository(Path.explode("~~")),
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
    strict: Boolean = false): Int =
  {
    val selection = Sessions.Selection.session(logic)
    val rc =
      if (!fresh && build(options, selection = selection,
            build_heap = build_heap, no_build = true, dirs = dirs).ok) 0
      else {
        progress.echo("Build started for Isabelle/" + logic + " ...")
        Build.build(options, selection = selection, progress = progress,
          build_heap = build_heap, fresh_build = fresh, dirs = dirs).rc
      }
    if (strict && rc != 0) error("Failed to build Isabelle/" + logic) else rc
  }
}
