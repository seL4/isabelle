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
      hostname: String = Isabelle_System.hostname(),
      numa_shuffling: Boolean = false,
      build_heap: Boolean = false,
      max_jobs: Int = 1,
      fresh_build: Boolean = false,
      no_build: Boolean = false,
      verbose: Boolean = false,
      session_setup: (String, Session) => Unit = (_, _) => (),
      instance: String = UUID.random().toString
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
      new Context(instance, store, deps, sessions, ordering, progress, hostname, numa_nodes,
        build_heap = build_heap, max_jobs = max_jobs, fresh_build = fresh_build,
        no_build = no_build, verbose = verbose, session_setup)
    }
  }

  final class Context private(
    val instance: String,
    val store: Sessions.Store,
    val deps: Sessions.Deps,
    sessions: Map[String, Session_Context],
    val ordering: Ordering[String],
    val progress: Progress,
    val hostname: String,
    val numa_nodes: List[Int],
    val build_heap: Boolean,
    val max_jobs: Int,
    val fresh_build: Boolean,
    val no_build: Boolean,
    val verbose: Boolean,
    val session_setup: (String, Session) => Unit,
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
    node_info: Build_Job.Node_Info,
    process_result: Process_Result
  ) {
    def ok: Boolean = process_result.ok
  }

  sealed case class State(
    serial: Long = 0,
    numa_index: Int = 0,
    pending: List[Entry] = Nil,
    running: Map[String, Build_Job] = Map.empty,
    results: Map[String, Build_Process.Result] = Map.empty
  ) {
    def numa_next(numa_nodes: List[Int]): (Option[Int], State) =
      if (numa_nodes.isEmpty) (None, this)
      else {
        val available = numa_nodes.zipWithIndex
        val used =
          Set.from(for (job <- running.valuesIterator; i <- job.node_info.numa_node) yield i)
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
      process_result: Process_Result,
      node_info: Build_Job.Node_Info = Build_Job.Node_Info.none
    ): State = {
      val result = Build_Process.Result(current, output_heap, node_info, process_result)
      copy(results = results + (name -> result))
    }

    def get_results(names: List[String]): List[Build_Process.Result] =
      names.map(results.apply)
  }


  /* SQL data model */

  object Data {
    val database = Path.explode("$ISABELLE_HOME_USER/build.db")

    def make_table(name: String, columns: List[SQL.Column], body: String = ""): SQL.Table =
      SQL.Table("isabelle_build" + if_proper(name, "_" + name), columns, body = body)

    object Generic {
      val instance = SQL.Column.string("instance")
      val name = SQL.Column.string("name")

      def sql_equal(instance: String = "", name: String = ""): SQL.Source =
        SQL.and(
          if_proper(instance, Generic.instance.equal(instance)),
          if_proper(name, Generic.name.equal(name)))

      def sql_member(instance: String = "", names: Iterable[String] = Nil): SQL.Source =
        SQL.and(
          if_proper(instance, Generic.instance.equal(instance)),
          if_proper(names, Generic.name.member(names)))
    }

    object Config {
      val instance = Generic.instance.make_primary_key
      val ml_identifier = SQL.Column.string("ml_identifier")
      val options = SQL.Column.string("options")

      val table = make_table("", List(instance, ml_identifier, options))
    }

    object State {
      val instance = Generic.instance.make_primary_key
      val serial = SQL.Column.long("serial")
      val numa_index = SQL.Column.int("numa_index")

      val table = make_table("state", List(instance, serial, numa_index))
    }

    object Pending {
      val name = Generic.name.make_primary_key
      val deps = SQL.Column.string("deps")
      val info = SQL.Column.string("info")

      val table = make_table("pending", List(name, deps, info))
    }

    object Running {
      val name = Generic.name.make_primary_key
      val hostname = SQL.Column.string("hostname")
      val numa_node = SQL.Column.int("numa_node")

      val table = make_table("running", List(name, hostname, numa_node))
    }

    object Results {
      val name = Generic.name.make_primary_key
      val hostname = SQL.Column.string("hostname")
      val numa_node = SQL.Column.string("numa_node")
      val rc = SQL.Column.int("rc")
      val out = SQL.Column.string("out")
      val err = SQL.Column.string("err")
      val timing_elapsed = SQL.Column.long("timing_elapsed")
      val timing_cpu = SQL.Column.long("timing_cpu")
      val timing_gc = SQL.Column.long("timing_gc")

      val table =
        make_table("results",
          List(name, hostname, numa_node, rc, out, err, timing_elapsed, timing_cpu, timing_gc))
    }

    def read_pending(db: SQL.Database): List[Entry] =
      db.using_statement(Pending.table.select() + SQL.order_by(List(Pending.name))) { stmt =>
        List.from(
          stmt.execute_query().iterator { res =>
            val name = res.string(Pending.name)
            val deps = res.string(Pending.deps)
            val info = res.string(Pending.info)
            Entry(name, split_lines(deps), info = JSON.Object.parse(info))
          })
      }

    def update_pending(db: SQL.Database, pending: List[Entry]): Boolean = {
      val old_pending = read_pending(db)
      val (delete, insert) = Library.symmetric_difference(old_pending, pending)

      if (delete.nonEmpty) {
        db.using_statement(
          Pending.table.delete() + SQL.where(Generic.sql_member(names = delete.map(_.name)))
        )(_.execute())
      }

      for (entry <- insert) {
        db.using_statement(Pending.table.insert()) { stmt =>
          stmt.string(1) = entry.name
          stmt.string(2) = cat_lines(entry.deps)
          stmt.string(3) = JSON.Format(entry.info)
          stmt.execute()
        }
      }

      delete.nonEmpty || insert.nonEmpty
    }

    def read_running(db: SQL.Database): List[Build_Job.Abstract] =
      db.using_statement(Running.table.select() + SQL.order_by(List(Running.name))) { stmt =>
        List.from(
          stmt.execute_query().iterator { res =>
            val name = res.string(Running.name)
            val hostname = res.string(Running.hostname)
            val numa_node = res.get_int(Running.numa_node)
            Build_Job.Abstract(name, Build_Job.Node_Info(hostname, numa_node))
          })
      }

    def update_running(db: SQL.Database, running: Map[String, Build_Job]): Boolean = {
      val old_running = read_running(db)
      val abs_running = running.valuesIterator.map(_.make_abstract).toList

      val (delete, insert) = Library.symmetric_difference(old_running, abs_running)

      if (delete.nonEmpty) {
        db.using_statement(
          Running.table.delete() + SQL.where(Generic.sql_member(names = delete.map(_.job_name)))
        )(_.execute())
      }

      for (job <- insert) {
        db.using_statement(Running.table.insert()) { stmt =>
          stmt.string(1) = job.job_name
          stmt.string(2) = job.node_info.hostname
          stmt.int(3) = job.node_info.numa_node
          stmt.execute()
        }
      }

      delete.nonEmpty || insert.nonEmpty
    }

    def read_results(db: SQL.Database, names: List[String] = Nil): Map[String, Build_Job.Result] =
      db.using_statement(
        Results.table.select() + if_proper(names, Results.name.where_member(names))
      ) { stmt =>
        Map.from(
          stmt.execute_query().iterator { res =>
            val name = res.string(Results.name)
            val hostname = res.string(Results.hostname)
            val numa_node = res.get_int(Results.numa_node)
            val rc = res.int(Results.rc)
            val out = res.string(Results.out)
            val err = res.string(Results.err)
            val timing_elapsed = res.long(Results.timing_elapsed)
            val timing_cpu = res.long(Results.timing_cpu)
            val timing_gc = res.long(Results.timing_gc)
            val node_info = Build_Job.Node_Info(hostname, numa_node)
            val process_result =
              Process_Result(rc,
                out_lines = split_lines(out),
                err_lines = split_lines(err),
                timing = Timing(Time.ms(timing_elapsed), Time.ms(timing_cpu), Time.ms(timing_gc)))
            name -> Build_Job.Result(node_info, process_result)
          })
      }

    def read_results_name(db: SQL.Database): Set[String] =
      db.using_statement(Results.table.select(List(Results.name))) { stmt =>
        Set.from(stmt.execute_query().iterator(_.string(Results.name)))
      }

    def update_results(db: SQL.Database, results: Map[String, Build_Process.Result]): Boolean = {
      val old_results = read_results_name(db)
      val insert = results.iterator.filterNot(p => !old_results.contains(p._1)).toList

      for ((name, result) <- insert) {
        val node_info = result.node_info
        val process_result = result.process_result
        db.using_statement(Results.table.insert()) { stmt =>
          stmt.string(1) = name
          stmt.string(2) = node_info.hostname
          stmt.int(3) = node_info.numa_node
          stmt.int(4) = process_result.rc
          stmt.string(5) = cat_lines(process_result.out_lines)
          stmt.string(6) = cat_lines(process_result.err_lines)
          stmt.long(7) = process_result.timing.elapsed.ms
          stmt.long(8) = process_result.timing.cpu.ms
          stmt.long(9) = process_result.timing.gc.ms
          stmt.execute()
        }
      }

      insert.nonEmpty
    }

    def write_config(db: SQL.Database, instance: String, hostname: String, options: Options): Unit =
      db.using_statement(Config.table.insert()) { stmt =>
        stmt.string(1) = instance
        stmt.string(2) = Isabelle_System.getenv("ML_IDENTIFIER")
        stmt.string(3) = options.make_prefs(Options.init(prefs = ""))
        stmt.execute()
      }

    def read_state(db: SQL.Database, instance: String): (Long, Int) =
      db.using_statement(
        State.table.select() + SQL.where(Generic.sql_equal(instance = instance))
      ) { stmt =>
        (stmt.execute_query().iterator { res =>
          val serial = res.long(State.serial)
          val numa_index = res.int(State.numa_index)
          (serial, numa_index)
        }).nextOption.getOrElse(error("No build state instance " + instance + " in database " + db))
      }

    def write_state(db: SQL.Database, instance: String, serial: Long, numa_index: Int): Unit = {
      db.using_statement(State.table.insert()) { stmt =>
        stmt.string(1) = instance
        stmt.long(2) = serial
        stmt.int(3) = numa_index
        stmt.execute()
      }
    }

    def reset_state(db: SQL.Database, instance: String): Unit =
      db.using_statement(
        State.table.delete() + SQL.where(Generic.sql_equal(instance = instance)))(_.execute())

    def init_database(db: SQL.Database, build_context: Build_Process.Context): Unit = {
      val tables =
        List(Config.table, State.table, Pending.table, Running.table, Results.table)

      for (table <- tables) db.create_table(table)

      val old_pending = Data.read_pending(db)
      if (old_pending.nonEmpty) {
        error("Cannot init build process, because of unfinished " +
          commas_quote(old_pending.map(_.name)))
      }

      for (table <- tables) db.using_statement(table.delete())(_.execute())

      write_config(db, build_context.instance, build_context.hostname, build_context.store.options)
      write_state(db, build_context.instance, 0, 0)
    }

    def update_database(db: SQL.Database, instance: String, state: State): State = {
      val ch1 = update_pending(db, state.pending)
      val ch2 = update_running(db, state.running)
      val ch3 = update_results(db, state.results)

      val (serial0, numa_index0) = read_state(db, instance)
      val serial = if (ch1 || ch2 || ch3) serial0 + 1 else serial0
      if (serial != serial0) {
        reset_state(db, instance)
        write_state(db, instance, serial, state.numa_index)
      }

      state.copy(serial = serial)
    }
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

class Build_Process(protected val build_context: Build_Process.Context) extends AutoCloseable {
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

  protected val database: Option[SQL.Database] =
    if (!build_options.bool("build_database") || true /*FIXME*/) None
    else if (store.database_server) Some(store.open_database_server())
    else Some(SQLite.open_database(Build_Process.Data.database))

  def close(): Unit = database.map(_.close())

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
        make_result(session_name, false, output_heap, process_result_tail, node_info = job.node_info)
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
          val node_info = Build_Job.Node_Info(build_context.hostname, numa_node)
          val job =
            new Build_Job.Build_Session(progress, session_background, store, do_store,
              resources, build_context.session_setup, input_heaps, node_info)
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

  protected def setup_database(): Unit =
    for (db <- database) {
      synchronized {
        db.transaction {
          Build_Process.Data.init_database(db, build_context)
        }
      }
      db.rebuild()
    }
  protected def sync_database(): Unit =
    for (db <- database) {
      synchronized {
        db.transaction {
          _state = Build_Process.Data.update_database(db, build_context.instance, _state)
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
      setup_database()
      while (!finished()) {
        if (progress.stopped) stop_running()

        for (job <- finished_running()) finish_job(job)

        next_pending() match {
          case Some(name) =>
            start_job(name)
          case None =>
            sync_database()
            sleep()
        }
      }
      synchronized {
        for ((name, result) <- _state.results) yield name -> result.process_result
      }
    }
  }
}
