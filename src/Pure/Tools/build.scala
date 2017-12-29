/*  Title:      Pure/Tools/build.scala
    Author:     Makarius
    Options:    :folding=explicit:

Build and manage Isabelle sessions.
*/

package isabelle


import java.io.{BufferedInputStream, FileInputStream,
  BufferedReader, InputStreamReader, IOException}
import java.util.zip.GZIPInputStream

import scala.collection.SortedSet
import scala.collection.mutable
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
    def load_timings(progress: Progress, store: Sessions.Store, name: String)
      : (List[Properties.T], Double) =
    {
      val no_timings: (List[Properties.T], Double) = (Nil, 0.0)

      store.find_database(name) match {
        case None => no_timings
        case Some(database) =>
          def ignore_error(msg: String) =
          {
            progress.echo_warning("Ignoring bad database: " +
              database.expand + (if (msg == "") "" else "\n" + msg))
            no_timings
          }
          try {
            using(SQLite.open_database(database))(db =>
            {
              val command_timings = store.read_command_timings(db, name)
              val session_timing =
                store.read_session_timing(db, name) match {
                  case Markup.Elapsed(t) => t
                  case _ => 0.0
                }
              (command_timings, session_timing)
            })
          }
          catch {
            case ERROR(msg) => ignore_error(msg)
            case exn: java.lang.Error => ignore_error(Exn.message(exn))
            case _: XML.Error => ignore_error("")
          }
      }
    }

    def apply(progress: Progress, sessions: Sessions.Structure, store: Sessions.Store): Queue =
    {
      val graph = sessions.build_graph
      val names = graph.keys

      val timings = names.map(name => (name, load_timings(progress, store, name)))
      val command_timings =
        Map(timings.map({ case (name, (ts, _)) => (name, ts) }): _*).withDefaultValue(Nil)
      val session_timing =
        Map(timings.map({ case (name, (_, t)) => (name, t) }): _*).withDefaultValue(0.0)

      def outdegree(name: String): Int = graph.imm_succs(name).size

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
          outdegree(name2) compare outdegree(name1) match {
            case 0 =>
              compare_timing(name2, name1) match {
                case 0 =>
                  sessions(name2).timeout compare sessions(name1).timeout match {
                    case 0 => name1 compare name2
                    case ord => ord
                  }
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
      if (it.hasNext) { val name = it.next; Some((name, graph.get_node(name))) }
      else None
    }
  }


  /* PIDE protocol handler */

  class Handler(progress: Progress, session: Session, session_name: String)
    extends Session.Protocol_Handler
  {
    val result_error: Promise[String] = Future.promise

    override def exit() { result_error.cancel }

    private def build_session_finished(msg: Prover.Protocol_Output): Boolean =
    {
      val error_message =
        try { Pretty.string_of(Symbol.decode_yxml(msg.text)) }
        catch { case ERROR(msg) => msg }
      result_error.fulfill(error_message)
      session.send_stop()
      true
    }

    private def loading_theory(msg: Prover.Protocol_Output): Boolean =
      msg.properties match {
        case Markup.Loading_Theory(name) =>
          progress.theory(session_name, name)
          true
        case _ => false
      }

    val functions =
      List(
        Markup.BUILD_SESSION_FINISHED -> build_session_finished _,
        Markup.LOADING_THEORY -> loading_theory _)
  }


  /* job: running prover process */

  private class Job(progress: Progress,
    name: String,
    val info: Sessions.Info,
    sessions: Sessions.Structure,
    deps: Sessions.Deps,
    store: Sessions.Store,
    do_output: Boolean,
    verbose: Boolean,
    pide: Boolean,
    val numa_node: Option[Int],
    command_timings: List[Properties.T])
  {
    val output = store.output_dir + Path.basic(name)
    def output_path: Option[Path] = if (do_output) Some(output) else None
    output.file.delete

    val options =
      numa_node match {
        case None => info.options
        case Some(n) => info.options.string("ML_process_policy") = NUMA.policy(n)
      }

    private val graph_file = Isabelle_System.tmp_file("session_graph", "pdf")
    isabelle.graphview.Graph_File.write(options, graph_file, deps(name).session_graph_display)

    private val future_result: Future[Process_Result] =
      Future.thread("build") {
        val parent = info.parent.getOrElse("")
        val base = deps(name)
        val args_yxml =
          YXML.string_of_body(
            {
              import XML.Encode._
              pair(list(pair(string, int)), pair(list(properties), pair(bool, pair(bool,
                pair(Path.encode, pair(list(pair(Path.encode, Path.encode)), pair(string,
                pair(string, pair(string, pair(string, pair(Path.encode,
                pair(list(pair(Options.encode, list(pair(string, properties)))),
                pair(list(string), pair(list(pair(string, string)), pair(list(string),
                pair(list(pair(string, string)), list(string)))))))))))))))))(
              (Symbol.codes, (command_timings, (do_output, (verbose,
                (store.browser_info, (info.document_files, (File.standard_path(graph_file),
                (parent, (info.chapter, (name, (Path.current,
                (info.theories, (base.known.sessions.toList,
                (base.global_theories.toList,
                (base.loaded_theories.keys,
                (base.dest_known_theories,
                info.bibtex_entries.map(_.info))))))))))))))))))
            })

        val env =
          Isabelle_System.settings() +
            ("ISABELLE_ML_DEBUGGER" -> options.bool("ML_debugger").toString)

        def save_heap: String =
          (if (info.theories.isEmpty) "" else "ML_Heap.share_common_data (); ") +
            "ML_Heap.save_child " + ML_Syntax.print_string_bytes(File.platform_path(output))

        if (pide && !Sessions.is_pure(name)) {
          val resources = new Resources(deps(parent))
          val session = new Session(options, resources)
          val handler = new Handler(progress, session, name)
          session.init_protocol_handler(handler)

          val session_result = Future.promise[Process_Result]

          Isabelle_Process.start(session, options, logic = parent,
            cwd = info.dir.file, env = env, sessions = Some(sessions), store = store,
            phase_changed =
            {
              case Session.Ready => session.protocol_command("build_session", args_yxml)
              case Session.Terminated(result) => session_result.fulfill(result)
              case _ =>
            })

          val result = session_result.join
          handler.result_error.join match {
            case "" => result
            case msg =>
              result.copy(
                rc = result.rc max 1,
                out_lines = result.out_lines ::: split_lines(Output.error_message_text(msg)))
          }
        }
        else {
          val args_file = Isabelle_System.tmp_file("build")
          File.write(args_file, args_yxml)

          val eval =
            "Command_Line.tool0 (fn () => (" +
            "Build.build " + ML_Syntax.print_string_bytes(File.standard_path(args_file)) +
            (if (do_output) "; " + save_heap else "") + "));"

          val process =
            if (Sessions.is_pure(name)) {
              ML_Process(options, raw_ml_system = true, cwd = info.dir.file,
                args =
                  (for ((root, _) <- Thy_Header.ml_roots) yield List("--use", root)).flatten :::
                  List("--eval", eval),
                env = env, sessions = Some(sessions), store = store,
                cleanup = () => args_file.delete)
            }
            else {
              ML_Process(options, parent, List("--eval", eval), cwd = info.dir.file,
                env = env, sessions = Some(sessions), store = store,
                cleanup = () => args_file.delete)
            }

          process.result(
            progress_stdout = (line: String) =>
              Library.try_unprefix("\floading_theory = ", line) match {
                case Some(theory) => progress.theory(name, theory)
                case None =>
              },
            progress_limit =
              options.int("process_output_limit") match {
                case 0 => None
                case m => Some(m * 1000000L)
              },
            strict = false)
        }
      }

    def terminate: Unit = future_result.cancel
    def is_finished: Boolean = future_result.is_finished

    private val timeout_request: Option[Event_Timer.Request] =
    {
      if (info.timeout > Time.zero)
        Some(Event_Timer.request(Time.now() + info.timeout) { terminate })
      else None
    }

    def join: Process_Result =
    {
      val result = future_result.join

      if (result.ok)
        Present.finish(progress, store.browser_info, graph_file, info, name)

      graph_file.delete

      val was_timeout =
        timeout_request match {
          case None => false
          case Some(request) => !request.cancel
        }

      if (result.interrupted) {
        if (was_timeout) result.error(Output.error_message_text("Timeout")).was_timeout
        else result.error(Output.error_message_text("Interrupt"))
      }
      else result
    }
  }



  /** build with results **/

  class Results private[Build](results: Map[String, (Option[Process_Result], Sessions.Info)])
  {
    def sessions: Set[String] = results.keySet
    def cancelled(name: String): Boolean = results(name)._1.isEmpty
    def apply(name: String): Process_Result = results(name)._1.getOrElse(Process_Result(1))
    def info(name: String): Sessions.Info = results(name)._2
    val rc =
      (0 /: results.iterator.map(
        { case (_, (Some(r), _)) => r.rc case (_, (None, _)) => 1 }))(_ max _)
    def ok: Boolean = rc == 0

    override def toString: String = rc.toString
  }

  def build(
    options: Options,
    progress: Progress = No_Progress,
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
    system_mode: Boolean = false,
    verbose: Boolean = false,
    pide: Boolean = false,
    requirements: Boolean = false,
    all_sessions: Boolean = false,
    base_sessions: List[String] = Nil,
    exclude_session_groups: List[String] = Nil,
    exclude_sessions: List[String] = Nil,
    session_groups: List[String] = Nil,
    sessions: List[String] = Nil,
    selection: Sessions.Selection = Sessions.Selection.empty): Results =
  {
    val build_options = options.int.update("completion_limit", 0).bool.update("ML_statistics", true)

    val store = Sessions.store(system_mode)


    /* session selection and dependencies */

    val full_sessions =
      Sessions.load_structure(build_options, dirs = dirs, select_dirs = select_dirs, infos = infos)

    def sources_stamp(deps: Sessions.Deps, name: String): String =
    {
      val digests =
        full_sessions(name).meta_digest :: deps.sources(name) ::: deps.imported_sources(name)
      SHA1.digest(cat_lines(digests.map(_.toString).sorted)).toString
    }

    val selection1 =
      Sessions.Selection(requirements, all_sessions, base_sessions, exclude_session_groups,
        exclude_sessions, session_groups, sessions) ++ selection

    val (selected_sessions, deps) =
    {
      val selected_sessions0 = full_sessions.selection(selection1)
      val deps0 =
        Sessions.deps(selected_sessions0, full_sessions.global_theories,
          progress = progress, inlined_files = true, verbose = verbose,
          list_files = list_files, check_keywords = check_keywords).check_errors

      if (soft_build && !fresh_build) {
        val outdated =
          selected_sessions0.build_topological_order.flatMap(name =>
            store.find_database(name) match {
              case Some(database) =>
                using(SQLite.open_database(database))(store.read_build(_, name)) match {
                  case Some(build)
                  if build.ok && build.sources == sources_stamp(deps0, name) => None
                  case _ => Some(name)
                }
              case None => Some(name)
            })
        val selected_sessions =
          full_sessions.selection(Sessions.Selection(sessions = outdated))
        val deps =
          Sessions.deps(selected_sessions, full_sessions.global_theories, inlined_files = true)
            .check_errors
        (selected_sessions, deps)
      }
      else (selected_sessions0, deps0)
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
        Mercurial.unknown_files(source_files).
          filterNot(path => exclude_files.contains(path.canonical_file))
      if (unknown_files.nonEmpty) {
        progress.echo_warning("Unknown files (not part of a Mercurial repository):" +
          unknown_files.map(path => path.expand.implode).sorted.mkString("\n  ", "\n  ", ""))
      }
    }


    /* main build process */

    val queue = Queue(progress, selected_sessions, store)

    store.prepare_output()

    // optional cleanup
    if (clean_build) {
      for (name <- full_sessions.build_descendants(full_sessions.build_selection(selection1))) {
        val files =
          List(Path.basic(name), store.database(name), store.log(name), store.log_gz(name)).
            map(store.output_dir + _).filter(_.is_file)
        if (files.nonEmpty) progress.echo("Cleaning " + name + " ...")
        if (!files.forall(p => p.file.delete)) progress.echo(name + " FAILED to delete")
      }
    }

    // scheduler loop
    case class Result(
      current: Boolean,
      heap_stamp: Option[String],
      process: Option[Process_Result],
      info: Sessions.Info)
    {
      def ok: Boolean =
        process match {
          case None => false
          case Some(res) => res.rc == 0
        }
    }

    def sleep()
    {
      try { Thread.sleep(500) }
      catch { case Exn.Interrupt() => Exn.Interrupt.impose() }
    }

    val numa_nodes = new NUMA.Nodes(numa_shuffling)

    @tailrec def loop(
      pending: Queue,
      running: Map[String, (List[String], Job)],
      results: Map[String, Result]): Map[String, Result] =
    {
      def used_node(i: Int): Boolean =
        running.iterator.exists(
          { case (_, (_, job)) => job.numa_node.isDefined && job.numa_node.get == i })

      if (pending.is_empty) results
      else {
        if (progress.stopped)
          for ((_, (_, job)) <- running) job.terminate

        running.find({ case (_, (_, job)) => job.is_finished }) match {
          case Some((name, (input_heaps, job))) =>
            //{{{ finish job

            val process_result = job.join

            val log_lines = process_result.out_lines.filterNot(_.startsWith("\f"))
            val process_result_tail =
            {
              val tail = job.info.options.int("process_output_tail")
              process_result.copy(
                out_lines =
                  "(see also " + (store.output_dir + store.log(name)).file.toString + ")" ::
                  (if (tail == 0) log_lines else log_lines.drop(log_lines.length - tail max 0)))
            }


            // write log file
            val heap_stamp =
              if (process_result.ok) {
                (store.output_dir + store.log(name)).file.delete
                val heap_stamp =
                  for (path <- job.output_path if path.is_file)
                    yield Sessions.write_heap_digest(path)

                File.write_gzip(store.output_dir + store.log_gz(name), terminate_lines(log_lines))

                heap_stamp
              }
              else {
                (store.output_dir + Path.basic(name)).file.delete
                (store.output_dir + store.log_gz(name)).file.delete

                File.write(store.output_dir + store.log(name), terminate_lines(log_lines))

                None
              }

            // write database
            {
              val database = store.output_dir + store.database(name)
              database.file.delete

              val build_log =
                Build_Log.Log_File(name, process_result.out_lines).
                  parse_session_info(
                    command_timings = true,
                    theory_timings = true,
                    ml_statistics = true,
                    task_statistics = true)

              using(SQLite.open_database(database))(db =>
                store.write_session_info(db, name,
                  build_log =
                    if (process_result.timeout) build_log.error("Timeout") else build_log,
                  build =
                    Session_Info(sources_stamp(deps, name), input_heaps, heap_stamp,
                      process_result.rc)))
            }

            // messages
            process_result.err_lines.foreach(progress.echo(_))

            if (process_result.ok)
              progress.echo("Finished " + name + " (" + process_result.timing.message_resources + ")")
            else {
              progress.echo(name + " FAILED")
              if (!process_result.interrupted) progress.echo(process_result_tail.out)
            }

            loop(pending - name, running - name,
              results + (name -> Result(false, heap_stamp, Some(process_result_tail), job.info)))
            //}}}
          case None if running.size < (max_jobs max 1) =>
            //{{{ check/start next job
            pending.dequeue(running.isDefinedAt(_)) match {
              case Some((name, info)) =>
                val ancestor_results =
                  selected_sessions.build_requirements(List(name)).filterNot(_ == name).
                    map(results(_))
                val ancestor_heaps = ancestor_results.flatMap(_.heap_stamp)

                val do_output = build_heap || Sessions.is_pure(name) || queue.is_inner(name)

                val (current, heap_stamp) =
                {
                  store.find_database_heap(name) match {
                    case Some((database, heap_stamp)) =>
                      using(SQLite.open_database(database))(store.read_build(_, name)) match {
                        case Some(build) =>
                          val current =
                            !fresh_build &&
                            build.ok &&
                            build.sources == sources_stamp(deps, name) &&
                            build.input_heaps == ancestor_heaps &&
                            build.output_heap == heap_stamp &&
                            !(do_output && heap_stamp.isEmpty)
                          (current, heap_stamp)
                        case None => (false, None)
                      }
                    case None => (false, None)
                  }
                }
                val all_current = current && ancestor_results.forall(_.current)

                if (all_current)
                  loop(pending - name, running,
                    results + (name -> Result(true, heap_stamp, Some(Process_Result(0)), info)))
                else if (no_build) {
                  if (verbose) progress.echo("Skipping " + name + " ...")
                  loop(pending - name, running,
                    results + (name -> Result(false, heap_stamp, Some(Process_Result(1)), info)))
                }
                else if (ancestor_results.forall(_.ok) && !progress.stopped) {
                  val numa_node = numa_nodes.next(used_node(_))
                  progress.echo((if (do_output) "Building " else "Running ") + name + " ...")
                  val job =
                    new Job(progress, name, info, selected_sessions, deps, store, do_output,
                      verbose, pide, numa_node, queue.command_timings(name))
                  loop(pending, running + (name -> (ancestor_heaps, job)), results)
                }
                else {
                  progress.echo(name + " CANCELLED")
                  loop(pending - name, running,
                    results + (name -> Result(false, heap_stamp, None, info)))
                }
              case None => sleep(); loop(pending, running, results)
            }
            ///}}}
          case None => sleep(); loop(pending, running, results)
        }
      }
    }


    /* build results */

    val results0 =
      if (deps.is_empty) {
        progress.echo_warning("Nothing to build")
        Map.empty[String, Result]
      }
      else loop(queue, Map.empty, Map.empty)

    val results =
      new Results(
        (for ((name, result) <- results0.iterator)
          yield (name, (result.process, result.info))).toMap)

    if (results.rc != 0 && (verbose || !no_build)) {
      val unfinished =
        (for {
          name <- results.sessions.iterator
          if !results(name).ok
         } yield name).toList.sorted
      progress.echo("Unfinished session(s): " + commas(unfinished))
    }


    /* global browser info */

    if (!no_build) {
      val browser_chapters =
        (for {
          (name, result) <- results0.iterator
          if result.ok
          info = full_sessions(name)
          if info.options.bool("browser_info")
        } yield (info.chapter, (name, info.description))).toList.groupBy(_._1).
            map({ case (chapter, es) => (chapter, es.map(_._2)) }).filterNot(_._2.isEmpty)

      for ((chapter, entries) <- browser_chapters)
        Present.update_chapter_index(store.browser_info, chapter, entries)

      if (browser_chapters.nonEmpty) Present.make_global_index(store.browser_info)
    }

    results
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("build", "build and manage Isabelle sessions", args =>
  {
    val build_options = Word.explode(Isabelle_System.getenv("ISABELLE_BUILD_OPTIONS"))

    var base_sessions: List[String] = Nil
    var select_dirs: List[Path] = Nil
    var numa_shuffling = false
    var pide = false
    var requirements = false
    var soft_build = false
    var exclude_session_groups: List[String] = Nil
    var all_sessions = false
    var build_heap = false
    var clean_build = false
    var dirs: List[Path] = Nil
    var fresh_build = false
    var session_groups: List[String] = Nil
    var max_jobs = 1
    var check_keywords: Set[String] = Set.empty
    var list_files = false
    var no_build = false
    var options = (Options.init() /: build_options)(_ + _)
    var system_mode = false
    var verbose = false
    var exclude_sessions: List[String] = Nil

    val getopts = Getopts("""
Usage: isabelle build [OPTIONS] [SESSIONS ...]

  Options are:
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -N           cyclic shuffling of NUMA CPU nodes (performance tuning)
    -P           build via PIDE protocol
    -R           operate on requirements of selected sessions
    -S           soft build: only observe changes of sources, not heap images
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -b           build heap images
    -c           clean build
    -d DIR       include session directory
    -f           fresh build
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs (default 1)
    -k KEYWORD   check theory sources for conflicts with proposed keywords
    -l           list session source files
    -n           no build -- test dependencies only
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -s           system build mode: produce output in ISABELLE_HOME
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Build and manage Isabelle sessions, depending on implicit settings:

""" + Library.prefix_lines("  ", Build_Log.Settings.show()) + "\n",
      "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
      "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
      "N" -> (_ => numa_shuffling = true),
      "P" -> (_ => pide = true),
      "R" -> (_ => requirements = true),
      "S" -> (_ => soft_build = true),
      "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
      "a" -> (_ => all_sessions = true),
      "b" -> (_ => build_heap = true),
      "c" -> (_ => clean_build = true),
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "f" -> (_ => fresh_build = true),
      "g:" -> (arg => session_groups = session_groups ::: List(arg)),
      "j:" -> (arg => max_jobs = Value.Int.parse(arg)),
      "k:" -> (arg => check_keywords = check_keywords + arg),
      "l" -> (_ => list_files = true),
      "n" -> (_ => no_build = true),
      "o:" -> (arg => options = options + arg),
      "s" -> (_ => system_mode = true),
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
        build(options, progress,
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
          system_mode = system_mode,
          verbose = verbose,
          pide = pide,
          requirements = requirements,
          all_sessions = all_sessions,
          base_sessions = base_sessions,
          exclude_session_groups = exclude_session_groups,
          exclude_sessions = exclude_sessions,
          session_groups = session_groups,
          sessions = sessions)
      }
    val end_date = Date.now()
    val elapsed_time = end_date.time - start_date.time

    if (verbose) {
      progress.echo("\nFinished at " + Build_Log.print_date(end_date))
    }

    val total_timing =
      (Timing.zero /: results.sessions.iterator.map(a => results(a).timing))(_ + _).
        copy(elapsed = elapsed_time)
    progress.echo(total_timing.message_resources)

    sys.exit(results.rc)
  })
}
