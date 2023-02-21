/*  Title:      Pure/Tools/build_process.scala
    Author:     Makarius

Build process for sessions, with build database, optional heap, and
optional presentation.
*/

package isabelle


import scala.math.Ordering
import scala.annotation.tailrec


object Build_Process {
  /* static context */

  object Session_Context {
    def empty(session: String, timeout: Time): Session_Context =
      new Session_Context(session, timeout, Time.zero, Nil)

    def apply(
      session: String,
      timeout: Time,
      store: Sessions.Store,
      progress: Progress = new Progress
    ): Session_Context = {
      store.try_open_database(session) match {
        case None => empty(session, timeout)
        case Some(db) =>
          def ignore_error(msg: String) = {
            progress.echo_warning("Ignoring bad database " + db +
              " for session " + quote(session) + (if (msg == "") "" else ":\n" + msg))
            empty(session, timeout)
          }
          try {
            val command_timings = store.read_command_timings(db, session)
            val elapsed =
              store.read_session_timing(db, session) match {
                case Markup.Elapsed(s) => Time.seconds(s)
                case _ => Time.zero
              }
            new Session_Context(session, timeout, elapsed, command_timings)
          }
          catch {
            case ERROR(msg) => ignore_error(msg)
            case exn: java.lang.Error => ignore_error(Exn.message(exn))
            case _: XML.Error => ignore_error("XML.Error")
          }
          finally { db.close() }
      }
    }
  }

  final class Session_Context(
    val session: String,
    val timeout: Time,
    val old_time: Time,
    val old_command_timings: List[Properties.T]
  ) {
    def is_empty: Boolean = old_time.is_zero && old_command_timings.isEmpty

    override def toString: String = session
  }

  object Context {
    def apply(
      store: Sessions.Store,
      deps: Sessions.Deps,
      progress: Progress = new Progress,
      build_heap: Boolean = false,
      numa_shuffling: Boolean = false,
      max_jobs: Int = 1,
      fresh_build: Boolean = false,
      no_build: Boolean = false,
      verbose: Boolean = false,
      session_setup: (String, Session) => Unit = (_, _) => ()
    ): Context = {
      val sessions_structure = deps.sessions_structure
      val build_graph = sessions_structure.build_graph

      val sessions =
        Map.from(
          for (name <- build_graph.keys_iterator)
          yield {
            val timeout = sessions_structure(name).timeout
            name -> Build_Process.Session_Context(name, timeout, store, progress = progress)
          })

      val sessions_time = {
        val maximals = build_graph.maximals.toSet
        def descendants_time(name: String): Double = {
          if (maximals.contains(name)) sessions(name).old_time.seconds
          else {
            val descendants = build_graph.all_succs(List(name)).toSet
            val g = build_graph.restrict(descendants)
            (0.0 :: g.maximals.flatMap { desc =>
              val ps = g.all_preds(List(desc))
              if (ps.exists(p => !sessions.isDefinedAt(p))) None
              else Some(ps.map(p => sessions(p).old_time.seconds).sum)
            }).max
          }
        }
        Map.from(
          for (name <- sessions.keysIterator)
          yield name -> descendants_time(name)).withDefaultValue(0.0)
      }

      val ordering =
        new Ordering[String] {
          def compare(name1: String, name2: String): Int =
            sessions_time(name2) compare sessions_time(name1) match {
              case 0 =>
                sessions(name2).timeout compare sessions(name1).timeout match {
                  case 0 => name1 compare name2
                  case ord => ord
                }
              case ord => ord
            }
        }

      val numa_nodes = NUMA.nodes(enabled = numa_shuffling)
      new Context(store, deps, sessions, ordering, progress, numa_nodes,
        build_heap = build_heap, max_jobs = max_jobs, fresh_build = fresh_build,
        no_build = no_build, verbose = verbose, session_setup)
    }
  }

  final class Context private(
    val store: Sessions.Store,
    val deps: Sessions.Deps,
    sessions: Map[String, Session_Context],
    val ordering: Ordering[String],
    val progress: Progress,
    val numa_nodes: List[Int],
    val build_heap: Boolean,
    val max_jobs: Int,
    val fresh_build: Boolean,
    val no_build: Boolean,
    val verbose: Boolean,
    val session_setup: (String, Session) => Unit
  ) {
    def sessions_structure: Sessions.Structure = deps.sessions_structure

    def apply(session: String): Session_Context =
      sessions.getOrElse(session, Session_Context.empty(session, Time.zero))

    def do_store(session: String): Boolean =
      build_heap || Sessions.is_pure(session) || !sessions_structure.build_graph.is_maximal(session)
  }


  /* dynamic state */

  case class Entry(name: String, deps: List[String], info: JSON.Object.T = JSON.Object.empty) {
    def is_ready: Boolean = deps.isEmpty
    def resolve(dep: String): Entry =
      if (deps.contains(dep)) copy(deps = deps.filterNot(_ == dep)) else this
  }

  case class Result(
    current: Boolean,
    output_heap: SHA1.Shasum,
    process_result: Process_Result
  ) {
    def ok: Boolean = process_result.ok
  }

  sealed case class State(
    numa_index: Int = 0,
    pending: List[Entry] = Nil,
    running: Map[String, Build_Job] = Map.empty,
    results: Map[String, Build_Process.Result] = Map.empty
  ) {
    def numa_next(numa_nodes: List[Int]): (Option[Int], State) =
      if (numa_nodes.isEmpty) (None, this)
      else {
        val available = numa_nodes.zipWithIndex
        val used = Set.from(for (job <- running.valuesIterator; i <- job.numa_node) yield i)
        val candidates = available.drop(numa_index) ::: available.take(numa_index)
        val (n, i) =
          candidates.find({ case (n, i) => i == numa_index && !used(n) }) orElse
          candidates.find({ case (n, _) => !used(n) }) getOrElse candidates.head
        (Some(n), copy(numa_index = (i + 1) % available.length))
      }

    def finished: Boolean = pending.isEmpty

    def remove_pending(name: String): State =
      copy(pending = pending.flatMap(
        entry => if (entry.name == name) None else Some(entry.resolve(name))))

    def is_running(name: String): Boolean = running.isDefinedAt(name)

    def stop_running(): Unit = running.valuesIterator.foreach(_.terminate())

    def finished_running(): List[Build_Job.Build_Session] =
      List.from(
        running.valuesIterator.flatMap {
          case job: Build_Job.Build_Session if job.is_finished => Some(job)
          case _ => None
        })

    def add_running(name: String, job: Build_Job): State =
      copy(running = running + (name -> job))

    def remove_running(name: String): State =
      copy(running = running - name)

    def make_result(
      name: String,
      current: Boolean,
      output_heap: SHA1.Shasum,
      process_result: Process_Result
    ): State = {
      val result = Build_Process.Result(current, output_heap, process_result)
      copy(results = results + (name -> result))
    }

    def get_results(names: List[String]): List[Build_Process.Result] =
      names.map(results.apply)
  }


  /* main process */

  def session_finished(session_name: String, process_result: Process_Result): String =
    "Finished " + session_name + " (" + process_result.timing.message_resources + ")"

  def session_timing(session_name: String, build_log: Build_Log.Session_Info): String = {
    val props = build_log.session_timing
    val threads = Markup.Session_Timing.Threads.unapply(props) getOrElse 1
    val timing = Markup.Timing_Properties.get(props)
    "Timing " + session_name + " (" + threads + " threads, " + timing.message_factor + ")"
  }
}

class Build_Process(protected val build_context: Build_Process.Context) {
  protected val store: Sessions.Store = build_context.store
  protected val build_options: Options = store.options
  protected val build_deps: Sessions.Deps = build_context.deps
  protected val progress: Progress = build_context.progress
  protected val verbose: Boolean = build_context.verbose

  protected val log: Logger =
    build_options.string("system_log") match {
      case "" => No_Logger
      case "-" => Logger.make(progress)
      case log_file => Logger.make(Some(Path.explode(log_file)))
    }

  // global state
  protected var _state: Build_Process.State = init_state()

  protected def init_state(): Build_Process.State =
    Build_Process.State(pending =
      (for ((name, (_, (preds, _))) <- build_context.sessions_structure.build_graph.iterator)
        yield Build_Process.Entry(name, preds.toList)).toList)

  protected def finished(): Boolean = synchronized { _state.finished }

  protected def next_pending(): Option[String] = synchronized {
    if (_state.running.size < (build_context.max_jobs max 1)) {
      _state.pending.filter(entry => entry.is_ready && !_state.is_running(entry.name))
        .sortBy(_.name)(build_context.ordering)
        .headOption.map(_.name)
    }
    else None
  }

  protected def stop_running(): Unit = synchronized { _state.stop_running() }

  protected def finished_running(): List[Build_Job.Build_Session] = synchronized {
    _state.finished_running()
  }

  protected def finish_job(job: Build_Job.Build_Session): Unit = {
    val session_name = job.session_name
    val process_result = job.join
    val output_heap = job.finish

    val log_lines = process_result.out_lines.filterNot(Protocol_Message.Marker.test)
    val process_result_tail = {
      val tail = job.info.options.int("process_output_tail")
      process_result.copy(
        out_lines =
          "(more details via \"isabelle log -H Error " + session_name + "\")" ::
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
      store.write_session_info(db, session_name, job.session_sources,
        build_log =
          if (process_result.timeout) build_log.error("Timeout") else build_log,
        build =
          Sessions.Build_Info(build_deps.sources_shasum(session_name), job.input_heaps,
            output_heap, process_result.rc, UUID.random().toString)))

    // messages
    process_result.err_lines.foreach(progress.echo)

    if (process_result.ok) {
      if (verbose) progress.echo(Build_Process.session_timing(session_name, build_log))
      progress.echo(Build_Process.session_finished(session_name, process_result))
    }
    else {
      progress.echo(session_name + " FAILED")
      if (!process_result.interrupted) progress.echo(process_result_tail.out)
    }

    synchronized {
      _state = _state.
        remove_pending(session_name).
        remove_running(session_name).
        make_result(session_name, false, output_heap, process_result_tail)
    }
  }

  protected def start_job(session_name: String): Unit = {
    val ancestor_results = synchronized {
      _state.get_results(
        build_deps.sessions_structure.build_requirements(List(session_name)).
          filterNot(_ == session_name))
    }
    val input_heaps =
      if (ancestor_results.isEmpty) {
        SHA1.shasum_meta_info(SHA1.digest(Path.explode("$POLYML_EXE")))
      }
      else SHA1.flat_shasum(ancestor_results.map(_.output_heap))

    val do_store = build_context.do_store(session_name)
    val (current, output_heap) = {
      store.try_open_database(session_name) match {
        case Some(db) =>
          using(db)(store.read_build(_, session_name)) match {
            case Some(build) =>
              val output_heap = store.find_heap_shasum(session_name)
              val current =
                !build_context.fresh_build &&
                build.ok &&
                build.sources == build_deps.sources_shasum(session_name) &&
                build.input_heaps == input_heaps &&
                build.output_heap == output_heap &&
                !(do_store && output_heap.is_empty)
              (current, output_heap)
            case None => (false, SHA1.no_shasum)
          }
        case None => (false, SHA1.no_shasum)
      }
    }
    val all_current = current && ancestor_results.forall(_.current)

    if (all_current) {
      synchronized {
        _state = _state.
          remove_pending(session_name).
          make_result(session_name, true, output_heap, Process_Result.ok)
      }
    }
    else if (build_context.no_build) {
      progress.echo_if(verbose, "Skipping " + session_name + " ...")
      synchronized {
        _state = _state.
          remove_pending(session_name).
          make_result(session_name, false, output_heap, Process_Result.error)
      }
    }
    else if (ancestor_results.forall(_.ok) && !progress.stopped) {
      progress.echo((if (do_store) "Building " else "Running ") + session_name + " ...")

      store.clean_output(session_name)
      using(store.open_database(session_name, output = true))(
        store.init_session_info(_, session_name))

      val session_background = build_deps.background(session_name)
      val resources =
        new Resources(session_background, log = log,
          command_timings = build_context(session_name).old_command_timings)

      val job =
        synchronized {
          val (numa_node, state1) = _state.numa_next(build_context.numa_nodes)
          val job =
            new Build_Job.Build_Session(progress, session_background, store, do_store,
              resources, build_context.session_setup, input_heaps, numa_node)
          _state = state1.add_running(session_name, job)
          job
        }
      job.start()
    }
    else {
      progress.echo(session_name + " CANCELLED")
      synchronized {
        _state = _state.
          remove_pending(session_name).
          make_result(session_name, false, output_heap, Process_Result.undefined)
      }
    }
  }

  protected def sleep(): Unit =
    Isabelle_Thread.interrupt_handler(_ => progress.stop()) {
      build_options.seconds("editor_input_delay").sleep()
    }

  def run(): Map[String, Process_Result] = {
    if (finished()) {
      progress.echo_warning("Nothing to build")
      Map.empty[String, Process_Result]
    }
    else {
      while (!finished()) {
        if (progress.stopped) stop_running()

        for (job <- finished_running()) finish_job(job)

        next_pending() match {
          case Some(name) => start_job(name)
          case None => sleep()
        }
      }
      synchronized {
        for ((name, result) <- _state.results) yield name -> result.process_result
      }
    }
  }
}
