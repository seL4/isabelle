/*  Title:      Pure/Tools/build_process.scala
    Author:     Makarius

Build process for sessions, with build database, optional heap, and
optional presentation.
*/

package isabelle


import scala.math.Ordering
import scala.collection.immutable.SortedSet
import scala.annotation.tailrec


object Build_Process {
  /* static information */

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
      progress: Progress = new Progress
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

      new Context(store, deps, sessions, ordering, progress)
    }
  }

  final class Context private(
    val store: Sessions.Store,
    val deps: Sessions.Deps,
    sessions: Map[String, Session_Context],
    val ordering: Ordering[String],
    val progress: Progress
  ) {
    def sessions_structure: Sessions.Structure = deps.sessions_structure

    def apply(session: String): Session_Context =
      sessions.getOrElse(session, Session_Context.empty(session, Time.zero))

    def build_heap(session: String): Boolean =
      Sessions.is_pure(session) || !sessions_structure.build_graph.is_maximal(session)
  }


  /* main */

  case class Result(
    current: Boolean,
    output_heap: SHA1.Shasum,
    process_result: Process_Result
  ) {
    def ok: Boolean = process_result.ok
  }
}

class Build_Process(
  build_context: Build_Process.Context,
  build_heap: Boolean = false,
  numa_shuffling: Boolean = false,
  max_jobs: Int = 1,
  fresh_build: Boolean = false,
  no_build: Boolean = false,
  verbose: Boolean = false,
  session_setup: (String, Session) => Unit = (_, _) => ()
) {
  private val store = build_context.store
  private val build_options = store.options
  private val build_deps = build_context.deps
  private val progress = build_context.progress

  private val log =
    build_options.string("system_log") match {
      case "" => No_Logger
      case "-" => Logger.make(progress)
      case log_file => Logger.make(Some(Path.explode(log_file)))
    }

  // global state
  private val _numa_nodes = new NUMA.Nodes(numa_shuffling)
  private var _build_graph = build_context.sessions_structure.build_graph
  private var _build_order = SortedSet.from(_build_graph.keys)(build_context.ordering)
  private var _running = Map.empty[String, Build_Job]
  private var _results = Map.empty[String, Build_Process.Result]

  private def remove_pending(name: String): Unit = synchronized {
    _build_graph = _build_graph.del_node(name)
    _build_order = _build_order - name
  }

  private def next_pending(): Option[String] = synchronized {
    _build_order.iterator
      .dropWhile(name => _running.isDefinedAt(name) || !_build_graph.is_minimal(name))
      .nextOption()
  }

  private def next_numa_node(): Option[Int] = synchronized {
    _numa_nodes.next(used =
      Set.from(for { job <- _running.valuesIterator; i <- job.numa_node } yield i))
  }

  private def job_running(name: String, job: Build_Job): Build_Job = synchronized {
    _running += (name -> job)
    job
  }

  private def remove_running(name: String): Unit = synchronized {
    _running -= name
  }

  private def session_finished(session_name: String, process_result: Process_Result): String =
    "Finished " + session_name + " (" + process_result.timing.message_resources + ")"

  private def session_timing(session_name: String, build_log: Build_Log.Session_Info): String = {
    val props = build_log.session_timing
    val threads = Markup.Session_Timing.Threads.unapply(props) getOrElse 1
    val timing = Markup.Timing_Properties.get(props)
    "Timing " + session_name + " (" + threads + " threads, " + timing.message_factor + ")"
  }

  private def finish_job(session_name: String, job: Build_Job): Unit = {
    val process_result = job.join

    val output_heap =
      if (process_result.ok && job.do_store && store.output_heap(session_name).is_file) {
        SHA1.shasum(ML_Heap.write_digest(store.output_heap(session_name)), session_name)
      }
      else SHA1.no_shasum

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
      if (verbose) progress.echo(session_timing(session_name, build_log))
      progress.echo(session_finished(session_name, process_result))
    }
    else {
      progress.echo(session_name + " FAILED")
      if (!process_result.interrupted) progress.echo(process_result_tail.out)
    }

    synchronized {
      remove_pending(session_name)
      remove_running(session_name)
      _results += (session_name -> Build_Process.Result(false, output_heap, process_result_tail))
    }
  }

  private def start_job(session_name: String): Unit = {
    val ancestor_results =
      build_deps.sessions_structure.build_requirements(List(session_name)).
        filterNot(_ == session_name).map(_results(_))
    val input_heaps =
      if (ancestor_results.isEmpty) {
        SHA1.shasum_meta_info(SHA1.digest(Path.explode("$POLYML_EXE")))
      }
      else SHA1.flat_shasum(ancestor_results.map(_.output_heap))

    val do_store = build_heap || build_context.build_heap(session_name)
    val (current, output_heap) = {
      store.try_open_database(session_name) match {
        case Some(db) =>
          using(db)(store.read_build(_, session_name)) match {
            case Some(build) =>
              val output_heap = store.find_heap_shasum(session_name)
              val current =
                !fresh_build &&
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
        remove_pending(session_name)
        _results += (session_name -> Build_Process.Result(true, output_heap, Process_Result.ok))
      }
    }
    else if (no_build) {
      progress.echo_if(verbose, "Skipping " + session_name + " ...")
      synchronized {
        remove_pending(session_name)
        _results += (session_name -> Build_Process.Result(false, output_heap, Process_Result.error))
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
          val numa_node = next_numa_node()
          job_running(session_name,
            new Build_Job(progress, session_background, store, do_store,
              resources, session_setup, input_heaps, numa_node))
        }
      job.start()
    }
    else {
      progress.echo(session_name + " CANCELLED")
      synchronized {
        remove_pending(session_name)
        _results += (session_name -> Build_Process.Result(false, output_heap, Process_Result.undefined))
      }
    }
  }

  private def sleep(): Unit =
    Isabelle_Thread.interrupt_handler(_ => progress.stop()) {
      build_options.seconds("editor_input_delay").sleep()
    }

  def run(): Map[String, Build_Process.Result] = {
    while (synchronized { !_build_graph.is_empty }) {
      if (progress.stopped) synchronized { _running.valuesIterator.foreach(_.terminate()) }

      synchronized { _running } .find({ case (_, job) => job.is_finished }) match {
        case Some((session_name, job)) => finish_job(session_name, job)
        case None if synchronized { _running.size } < (max_jobs max 1) =>
          next_pending() match {
            case Some(session_name) => start_job(session_name)
            case None => sleep()
          }
        case None => sleep()
      }
    }

    synchronized { _results }
  }
}
