/*  Title:      Pure/Tools/build_process.scala
    Author:     Makarius

Build process for sessions, with build database, optional heap, and
optional presentation.
*/

package isabelle


import scala.math.Ordering
import scala.annotation.tailrec


object Build_Process {
  /** static context **/

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



  /** dynamic state **/

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

    def finished_running(): List[Build_Job] =
      List.from(running.valuesIterator.filter(_.is_finished))

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



  /** SQL data model **/

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

    object Base {
      val instance = Generic.instance.make_primary_key
      val ml_platform = SQL.Column.string("ml_platform")
      val options = SQL.Column.string("options")

      val table = make_table("", List(instance, ml_platform, options))
    }

    object Serial {
      val serial = SQL.Column.long("serial")

      val table = make_table("serial", List(serial))
    }

    object Node_Info {
      val hostname = SQL.Column.string("hostname").make_primary_key
      val numa_index = SQL.Column.int("numa_index")

      val table = make_table("node_info", List(hostname, numa_index))
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

    def get_serial(db: SQL.Database): Long =
      db.using_statement(Serial.table.select())(stmt =>
        stmt.execute_query().iterator(_.long(Serial.serial)).nextOption.getOrElse(0L))

    def set_serial(db: SQL.Database, serial: Long): Unit =
      if (get_serial(db) != serial) {
        db.using_statement(Serial.table.delete())(_.execute())
        db.using_statement(Serial.table.insert()) { stmt =>
          stmt.long(1) = serial
          stmt.execute()
        }
      }

    def read_numa_index(db: SQL.Database, hostname: String): Int =
      db.using_statement(
        Node_Info.table.select(List(Node_Info.numa_index),
          sql = Node_Info.hostname.where_equal(hostname))
      )(stmt => stmt.execute_query().iterator(_.int(Node_Info.numa_index)).nextOption.getOrElse(0))

    def update_numa_index(db: SQL.Database, hostname: String, numa_index: Int): Boolean =
      if (read_numa_index(db, hostname) != numa_index) {
        db.using_statement(
          Node_Info.table.delete(sql = Node_Info.hostname.where_equal(hostname))
        )(_.execute())
        db.using_statement(Node_Info.table.insert()) { stmt =>
          stmt.string(1) = hostname
          stmt.int(2) = numa_index
          stmt.execute()
        }
        true
      }
      else false

    def read_pending(db: SQL.Database): List[Entry] =
      db.using_statement(Pending.table.select(sql = SQL.order_by(List(Pending.name)))) { stmt =>
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
          Pending.table.delete(
            sql = SQL.where(Generic.sql_member(names = delete.map(_.name)))))(_.execute())
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
      db.using_statement(Running.table.select(sql = SQL.order_by(List(Running.name)))) { stmt =>
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
          Running.table.delete(
            sql = SQL.where(Generic.sql_member(names = delete.map(_.job_name)))))(_.execute())
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
        Results.table.select(sql = if_proper(names, Results.name.where_member(names)))) { stmt =>
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
      db.using_statement(Results.table.select(List(Results.name)))(stmt =>
        Set.from(stmt.execute_query().iterator(_.string(Results.name))))

    def update_results(db: SQL.Database, results: Map[String, Build_Process.Result]): Boolean = {
      val old_results = read_results_name(db)
      val insert = results.iterator.filterNot(p => old_results.contains(p._1)).toList

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

    def init_database(db: SQL.Database, build_context: Build_Process.Context): Unit = {
      val tables =
        List(
          Base.table,
          Serial.table,
          Node_Info.table,
          Pending.table,
          Running.table,
          Results.table)

      for (table <- tables) db.create_table(table)

      val old_pending = Data.read_pending(db)
      if (old_pending.nonEmpty) {
        error("Cannot init build process, because of unfinished " +
          commas_quote(old_pending.map(_.name)))
      }

      for (table <- tables) db.using_statement(table.delete())(_.execute())

      db.using_statement(Base.table.insert()) { stmt =>
        stmt.string(1) = build_context.instance
        stmt.string(2) = Isabelle_System.getenv("ML_PLATFORM")
        stmt.string(3) = build_context.store.options.make_prefs(Options.init(prefs = ""))
        stmt.execute()
      }
    }

    def update_database(
      db: SQL.Database,
      instance: String,
      hostname: String,
      state: State
    ): State = {
      val changed =
        List(
          update_numa_index(db, hostname, state.numa_index),
          update_pending(db, state.pending),
          update_running(db, state.running),
          update_results(db, state.results))

      val serial0 = get_serial(db)
      val serial = if (changed.exists(identity)) serial0 + 1 else serial0

      set_serial(db, serial)
      state.copy(serial = serial)
    }
  }
}



/** main process **/

class Build_Process(protected val build_context: Build_Process.Context)
extends AutoCloseable {
  /* context */

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


  /* database */

  protected val database: Option[SQL.Database] =
    if (!build_options.bool("build_database_test")) None
    else if (store.database_server) Some(store.open_database_server())
    else {
      val db = SQLite.open_database(Build_Process.Data.database)
      try { Isabelle_System.chmod("600", Build_Process.Data.database) }
      catch { case exn: Throwable => db.close(); throw exn }
      Some(db)
    }

  def close(): Unit = database.foreach(_.close())

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
          _state =
            Build_Process.Data.update_database(
              db, build_context.instance, build_context.hostname, _state)
        }
      }
    }


  /* global state */

  protected var _state: Build_Process.State = init_state(Build_Process.State())

  protected def init_state(state: Build_Process.State): Build_Process.State = {
    val old_pending = state.pending.iterator.map(_.name).toSet
    val new_pending =
      List.from(
        for {
          (name, (_, (preds, _))) <- build_context.sessions_structure.build_graph.iterator
          if !old_pending(name)
        } yield Build_Process.Entry(name, preds.toList))
    state.copy(pending = new_pending ::: state.pending)
  }

  protected def next_pending(): Option[String] = synchronized {
    if (_state.running.size < (build_context.max_jobs max 1)) {
      _state.pending.filter(entry => entry.is_ready && !_state.is_running(entry.name))
        .sortBy(_.name)(build_context.ordering)
        .headOption.map(_.name)
    }
    else None
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
      val session_heaps =
        session_background.info.parent match {
          case None => Nil
          case Some(logic) => ML_Process.session_heaps(store, session_background, logic = logic)
        }

      val resources =
        new Resources(session_background, log = log,
          command_timings = build_context(session_name).old_command_timings)

      val job =
        synchronized {
          val (numa_node, state1) = _state.numa_next(build_context.numa_nodes)
          val node_info = Build_Job.Node_Info(build_context.hostname, numa_node)
          val job =
            new Build_Job.Build_Session(progress, verbose, session_background, session_heaps,
              store, do_store, resources, build_context.session_setup,
              build_deps.sources_shasum(session_name), input_heaps, node_info)
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


  /* run */

  protected def sleep(): Unit =
    Isabelle_Thread.interrupt_handler(_ => progress.stop()) {
      build_options.seconds("editor_input_delay").sleep()
    }

  def run(): Map[String, Process_Result] = {
    def finished(): Boolean = synchronized { _state.finished }

    if (finished()) {
      progress.echo_warning("Nothing to build")
      Map.empty[String, Process_Result]
    }
    else {
      setup_database()
      while (!finished()) {
        if (progress.stopped) synchronized { _state.stop_running() }

        for (job <- synchronized { _state.finished_running() }) {
          val job_name = job.job_name
          val (process_result, output_heap) = job.finish
          synchronized {
            _state = _state.
              remove_pending(job_name).
              remove_running(job_name).
              make_result(job_name, false, output_heap, process_result, node_info = job.node_info)
          }
        }

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
