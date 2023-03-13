/*  Title:      Pure/Tools/build_process.scala
    Author:     Makarius

Build process for sessions, with build database, optional heap, and
optional presentation.
*/

package isabelle


import scala.collection.immutable.SortedMap
import scala.math.Ordering
import scala.annotation.tailrec


object Build_Process {
  /** static context **/

  object Context {
    def apply(
      store: Sessions.Store,
      build_deps: Sessions.Deps,
      progress: Progress = new Progress,
      ml_platform: String = Isabelle_System.getenv("ML_PLATFORM"),
      hostname: String = Isabelle_System.hostname(),
      numa_shuffling: Boolean = false,
      build_heap: Boolean = false,
      max_jobs: Int = 1,
      fresh_build: Boolean = false,
      no_build: Boolean = false,
      session_setup: (String, Session) => Unit = (_, _) => (),
      build_uuid: String = UUID.random().toString,
      master: Boolean = false,
    ): Context = {
      val sessions_structure = build_deps.sessions_structure
      val build_graph = sessions_structure.build_graph

      val sessions =
        Map.from(
          for ((name, (info, _)) <- build_graph.iterator)
          yield {
            val deps = info.parent.toList
            val ancestors = sessions_structure.build_requirements(deps)
            val sources_shasum = build_deps.sources_shasum(name)
            val session_context =
              Build_Job.Session_Context.load(
                build_uuid, name, deps, ancestors, info.session_prefs, sources_shasum,
                info.timeout, store, progress = progress)
            name -> session_context
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

      val numa_nodes = Host.numa_nodes(enabled = numa_shuffling)
      new Context(store, build_deps, sessions, ordering, ml_platform, hostname, numa_nodes,
        build_heap = build_heap, max_jobs = max_jobs, fresh_build = fresh_build,
        no_build = no_build, session_setup, build_uuid = build_uuid, master = master)
    }
  }

  final class Context private(
    val store: Sessions.Store,
    val build_deps: Sessions.Deps,
    val sessions: State.Sessions,
    val ordering: Ordering[String],
    val ml_platform: String,
    val hostname: String,
    val numa_nodes: List[Int],
    val build_heap: Boolean,
    val max_jobs: Int,
    val fresh_build: Boolean,
    val no_build: Boolean,
    val session_setup: (String, Session) => Unit,
    val build_uuid: String,
    val master: Boolean
  ) {
    override def toString: String =
      "Build_Process.Context(build_uuid = " + quote(build_uuid) + ")"

    def build_options: Options = store.options

    def sessions_structure: Sessions.Structure = build_deps.sessions_structure

    def sources_shasum(name: String): SHA1.Shasum = sessions(name).sources_shasum

    def old_command_timings(name: String): List[Properties.T] =
      sessions.get(name) match {
        case Some(session_context) =>
          Properties.uncompress(session_context.old_command_timings_blob, cache = store.cache)
        case None => Nil
      }

    def prepare_database(): Unit = {
      using_option(store.open_build_database()) { db =>
        db.transaction {
          Data.all_tables.create_lock(db)
          Data.clean_build(db)
        }
        db.rebuild()
      }
    }

    def store_heap(name: String): Boolean =
      build_heap || Sessions.is_pure(name) ||
      sessions.valuesIterator.exists(_.ancestors.contains(name))

    def worker_active: Boolean = max_jobs > 0
  }



  /** dynamic state **/

  type Progress_Messages = SortedMap[Long, Progress.Message]

  case class Worker(
    worker_uuid: String,
    build_uuid: String,
    hostname: String,
    java_pid: Long,
    java_start: Date,
    start: Date,
    stamp: Date,
    stop: Option[Date],
    serial: Long
  )

  case class Task(
    name: String,
    deps: List[String],
    info: JSON.Object.T = JSON.Object.empty
  ) {
    def is_ready: Boolean = deps.isEmpty
    def resolve(dep: String): Task =
      if (deps.contains(dep)) copy(deps = deps.filterNot(_ == dep)) else this
  }

  case class Job(
    name: String,
    worker_uuid: String,
    node_info: Host.Node_Info,
    build: Option[Build_Job]
  ) {
    def no_build: Job = copy(build = None)
  }

  case class Result(
    process_result: Process_Result,
    output_shasum: SHA1.Shasum,
    node_info: Host.Node_Info,
    current: Boolean
  ) {
    def ok: Boolean = process_result.ok
  }

  object State {
    type Sessions = Map[String, Build_Job.Session_Context]
    type Workers = List[Worker]
    type Pending = List[Task]
    type Running = Map[String, Job]
    type Results = Map[String, Result]

    def inc_serial(serial: Long): Long = {
      require(serial < java.lang.Long.MAX_VALUE, "serial overflow")
      serial + 1
    }
  }

  sealed case class State(
    serial: Long = 0,
    progress_seen: Long = 0,
    numa_next: Int = 0,
    sessions: State.Sessions = Map.empty,   // static build targets
    workers: State.Workers = Nil,           // available worker processes
    pending: State.Pending = Nil,           // dynamic build "queue"
    running: State.Running = Map.empty,     // presently running jobs
    results: State.Results = Map.empty      // finished results
  ) {
    require(serial >= 0, "serial underflow")
    def inc_serial: State = copy(serial = State.inc_serial(serial))
    def set_serial(i: Long): State = {
      require(serial <= i, "non-monotonic change of serial")
      copy(serial = i)
    }

    def progress_serial(message_serial: Long = serial): State =
      if (message_serial > progress_seen) copy(progress_seen = message_serial)
      else error("Bad serial " + message_serial + " for progress output (already seen)")

    def set_workers(new_workers: State.Workers): State = copy(workers = new_workers)

    def next_numa_node(numa_nodes: List[Int]): (Option[Int], State) =
      if (numa_nodes.isEmpty) (None, this)
      else {
        val available = numa_nodes.zipWithIndex
        val used =
          Set.from(for (job <- running.valuesIterator; i <- job.node_info.numa_node) yield i)

        val numa_index = available.collectFirst({ case (n, i) if n == numa_next => i }).getOrElse(0)
        val candidates = available.drop(numa_index) ::: available.take(numa_index)
        val (n, i) =
          candidates.find({ case (n, i) => i == numa_index && !used(n) }) orElse
          candidates.find({ case (n, _) => !used(n) }) getOrElse candidates.head

        (Some(n), copy(numa_next = numa_nodes((i + 1) % numa_nodes.length)))
      }

    def finished: Boolean = pending.isEmpty

    def remove_pending(name: String): State =
      copy(pending = pending.flatMap(
        entry => if (entry.name == name) None else Some(entry.resolve(name))))

    def is_running(name: String): Boolean = running.isDefinedAt(name)

    def stop_running(): Unit =
      for (job <- running.valuesIterator; build <- job.build) build.cancel()

    def finished_running(): List[Build_Job] =
      List.from(
        for (job <- running.valuesIterator; build <- job.build if build.is_finished)
        yield build)

    def add_running(job: Job): State =
      copy(running = running + (job.name -> job))

    def remove_running(name: String): State =
      copy(running = running - name)

    def make_result(
      name: String,
      process_result: Process_Result,
      output_shasum: SHA1.Shasum,
      node_info: Host.Node_Info = Host.Node_Info.none,
      current: Boolean = false
    ): State = {
      val entry = name -> Build_Process.Result(process_result, output_shasum, node_info, current)
      copy(results = results + entry)
    }
  }



  /** SQL data model **/

  object Data {
    def make_table(name: String, columns: List[SQL.Column], body: String = ""): SQL.Table =
      SQL.Table("isabelle_build" + if_proper(name, "_" + name), columns, body = body)

    object Generic {
      val build_uuid = SQL.Column.string("build_uuid")
      val worker_uuid = SQL.Column.string("worker_uuid")
      val name = SQL.Column.string("name")

      def sql(
        build_uuid: String = "",
        worker_uuid: String = "",
        name: String = "",
        names: Iterable[String] = Nil
      ): SQL.Source =
        SQL.and(
          if_proper(build_uuid, Generic.build_uuid.equal(build_uuid)),
          if_proper(worker_uuid, Generic.worker_uuid.equal(worker_uuid)),
          if_proper(name, Generic.name.equal(name)),
          if_proper(names, Generic.name.member(names)))
    }


    /* base table */

    object Base {
      val build_uuid = Generic.build_uuid.make_primary_key
      val ml_platform = SQL.Column.string("ml_platform")
      val options = SQL.Column.string("options")
      val start = SQL.Column.date("start")
      val stop = SQL.Column.date("stop")

      val table = make_table("", List(build_uuid, ml_platform, options, start, stop))
    }

    def start_build(
      db: SQL.Database,
      build_uuid: String,
      ml_platform: String,
      options: String
    ): Unit = {
      db.execute_statement(Base.table.insert(), body =
        { stmt =>
          stmt.string(1) = build_uuid
          stmt.string(2) = ml_platform
          stmt.string(3) = options
          stmt.date(4) = db.now()
          stmt.date(5) = None
        })
    }

    def stop_build(db: SQL.Database, build_uuid: String): Unit =
      db.execute_statement(
        Base.table.update(List(Base.stop), sql = SQL.where(Generic.sql(build_uuid = build_uuid))),
        body = { stmt => stmt.date(1) = db.now() })

    def clean_build(db: SQL.Database): Unit = {
      val old =
        db.execute_query_statement(
          Base.table.select(List(Base.build_uuid), sql = SQL.where(Base.stop.defined)),
          List.from[String], res => res.string(Base.build_uuid))

      if (old.nonEmpty) {
        for (table <- List(Base.table, Sessions.table, Progress.table, Workers.table)) {
          db.execute_statement(table.delete(sql = Generic.build_uuid.where_member(old)))
        }
      }
    }


    /* sessions */

    object Sessions {
      val name = Generic.name.make_primary_key
      val deps = SQL.Column.string("deps")
      val ancestors = SQL.Column.string("ancestors")
      val options = SQL.Column.string("options")
      val sources = SQL.Column.string("sources")
      val timeout = SQL.Column.long("timeout")
      val old_time = SQL.Column.long("old_time")
      val old_command_timings = SQL.Column.bytes("old_command_timings")
      val build_uuid = Generic.build_uuid

      val table = make_table("sessions",
        List(name, deps, ancestors, options, sources, timeout,
          old_time, old_command_timings, build_uuid))
    }

    def read_sessions_domain(db: SQL.Database): Set[String] =
      db.execute_query_statement(
        Sessions.table.select(List(Sessions.name)),
        Set.from[String], res => res.string(Sessions.name))

    def read_sessions(db: SQL.Database, names: Iterable[String] = Nil): State.Sessions =
      db.execute_query_statement(
        Sessions.table.select(sql = if_proper(names, Sessions.name.where_member(names))),
        Map.from[String, Build_Job.Session_Context],
        { res =>
          val name = res.string(Sessions.name)
          val deps = split_lines(res.string(Sessions.deps))
          val ancestors = split_lines(res.string(Sessions.ancestors))
          val options = res.string(Sessions.options)
          val sources_shasum = SHA1.fake_shasum(res.string(Sessions.sources))
          val timeout = Time.ms(res.long(Sessions.timeout))
          val old_time = Time.ms(res.long(Sessions.old_time))
          val old_command_timings_blob = res.bytes(Sessions.old_command_timings)
          val build_uuid = res.string(Sessions.build_uuid)
          name -> Build_Job.Session_Context(name, deps, ancestors, options, sources_shasum,
            timeout, old_time, old_command_timings_blob, build_uuid)
        }
      )

    def update_sessions(db:SQL.Database, sessions: State.Sessions): Boolean = {
      val old_sessions = read_sessions_domain(db)
      val insert = sessions.iterator.filterNot(p => old_sessions.contains(p._1)).toList

      for ((name, session) <- insert) {
        db.execute_statement(Sessions.table.insert(), body =
          { stmt =>
            stmt.string(1) = name
            stmt.string(2) = cat_lines(session.deps)
            stmt.string(3) = cat_lines(session.ancestors)
            stmt.string(4) = session.session_prefs
            stmt.string(5) = session.sources_shasum.toString
            stmt.long(6) = session.timeout.ms
            stmt.long(7) = session.old_time.ms
            stmt.bytes(8) = session.old_command_timings_blob
            stmt.string(9) = session.build_uuid
          })
      }

      insert.nonEmpty
    }


    /* progress */

    object Progress {
      val serial = SQL.Column.long("serial").make_primary_key
      val kind = SQL.Column.int("kind")
      val text = SQL.Column.string("text")
      val verbose = SQL.Column.bool("verbose")
      val build_uuid = Generic.build_uuid

      val table = make_table("progress", List(serial, kind, text, verbose, build_uuid))
    }

    def read_progress(db: SQL.Database, seen: Long = 0, build_uuid: String = ""): Progress_Messages =
      db.execute_query_statement(
        Progress.table.select(
          sql =
            SQL.where(
              SQL.and(
                if (seen <= 0) "" else Progress.serial.ident + " > " + seen,
                Generic.sql(build_uuid = build_uuid)))),
        SortedMap.from[Long, isabelle.Progress.Message],
        { res =>
          val serial = res.long(Progress.serial)
          val kind = isabelle.Progress.Kind(res.int(Progress.kind))
          val text = res.string(Progress.text)
          val verbose = res.bool(Progress.verbose)
          serial -> isabelle.Progress.Message(kind, text, verbose = verbose)
        }
      )

    def write_progress(
      db: SQL.Database,
      message_serial: Long,
      message: isabelle.Progress.Message,
      build_uuid: String
    ): Unit = {
      db.execute_statement(Progress.table.insert(), body =
        { stmt =>
          stmt.long(1) = message_serial
          stmt.int(2) = message.kind.id
          stmt.string(3) = message.text
          stmt.bool(4) = message.verbose
          stmt.string(5) = build_uuid
        })
    }


    /* workers */

    object Workers {
      val worker_uuid = Generic.worker_uuid.make_primary_key
      val build_uuid = Generic.build_uuid
      val hostname = SQL.Column.string("hostname")
      val java_pid = SQL.Column.long("java_pid")
      val java_start = SQL.Column.date("java_start")
      val start = SQL.Column.date("start")
      val stamp = SQL.Column.date("stamp")
      val stop = SQL.Column.date("stop")
      val serial = SQL.Column.long("serial")

      val table = make_table("workers",
        List(worker_uuid, build_uuid, hostname, java_pid, java_start, start, stamp, stop, serial))

      val serial_max = serial.copy(expr = "MAX(" + serial.ident + ")")
    }

    def read_workers(
      db: SQL.Database,
      build_uuid: String = "",
      worker_uuid: String = ""
    ): State.Workers = {
      db.execute_query_statement(
        Workers.table.select(sql =
          SQL.where(Generic.sql(build_uuid = build_uuid, worker_uuid = worker_uuid))),
          List.from[Worker],
          { res =>
            Worker(
              worker_uuid = res.string(Workers.worker_uuid),
              build_uuid = res.string(Workers.build_uuid),
              hostname = res.string(Workers.hostname),
              java_pid = res.long(Workers.java_pid),
              java_start = res.date(Workers.java_start),
              start = res.date(Workers.start),
              stamp = res.date(Workers.stamp),
              stop = res.get_date(Workers.stop),
              serial = res.long(Workers.serial))
          })
    }

    def serial_max(db: SQL.Database): Long =
      db.execute_query_statementO[Long](
        Workers.table.select(List(Workers.serial_max)),
        res => res.long(Workers.serial)
      ).getOrElse(0L)

    def start_worker(
      db: SQL.Database,
      worker_uuid: String,
      build_uuid: String,
      hostname: String,
      java_pid: Long,
      java_start: Date
    ): Long = {
      def err(msg: String): Nothing =
        error("Cannot start worker " + worker_uuid + if_proper(msg, "\n" + msg))

      val build_stop =
        db.execute_query_statementO(
          Base.table.select(List(Base.stop),
            sql = SQL.where(Generic.sql(build_uuid = build_uuid))),
          res => res.get_date(Base.stop))

      build_stop match {
        case Some(None) =>
        case Some(Some(_)) => err("for already stopped build process " + build_uuid)
        case None => err("for unknown build process " + build_uuid)
      }

      val serial = serial_max(db)
      db.execute_statement(Workers.table.insert(), body =
        { stmt =>
          val now = db.now()
          stmt.string(1) = worker_uuid
          stmt.string(2) = build_uuid
          stmt.string(3) = hostname
          stmt.long(4) = java_pid
          stmt.date(5) = java_start
          stmt.date(6) = now
          stmt.date(7) = now
          stmt.date(8) = None
          stmt.long(9) = serial
        })
      serial
    }

    def stamp_worker(
      db: SQL.Database,
      worker_uuid: String,
      serial: Long,
      stop: Boolean = false
    ): Unit = {
      val sql =
        Workers.table.update(List(Workers.stamp, Workers.stop, Workers.serial),
          sql = SQL.where(Generic.sql(worker_uuid = worker_uuid)))
      db.execute_statement(sql, body =
        { stmt =>
          val now = db.now()
          stmt.date(1) = now
          stmt.date(2) = if (stop) Some(now) else None
          stmt.long(3) = serial
        })
    }


    /* pending jobs */

    object Pending {
      val name = Generic.name.make_primary_key
      val deps = SQL.Column.string("deps")
      val info = SQL.Column.string("info")

      val table = make_table("pending", List(name, deps, info))
    }

    def read_pending(db: SQL.Database): List[Task] =
      db.execute_query_statement(
        Pending.table.select(sql = SQL.order_by(List(Pending.name))),
        List.from[Task],
        { res =>
          val name = res.string(Pending.name)
          val deps = res.string(Pending.deps)
          val info = res.string(Pending.info)
          Task(name, split_lines(deps), info = JSON.Object.parse(info))
        })

    def update_pending(db: SQL.Database, pending: State.Pending): Boolean = {
      val old_pending = read_pending(db)
      val (delete, insert) = Library.symmetric_difference(old_pending, pending)

      if (delete.nonEmpty) {
        db.execute_statement(
          Pending.table.delete(sql = SQL.where(Generic.sql(names = delete.map(_.name)))))
      }

      for (entry <- insert) {
        db.execute_statement(Pending.table.insert(), body =
          { stmt =>
            stmt.string(1) = entry.name
            stmt.string(2) = cat_lines(entry.deps)
            stmt.string(3) = JSON.Format(entry.info)
          })
      }

      delete.nonEmpty || insert.nonEmpty
    }


    /* running jobs */

    object Running {
      val name = Generic.name.make_primary_key
      val worker_uuid = Generic.worker_uuid
      val hostname = SQL.Column.string("hostname")
      val numa_node = SQL.Column.int("numa_node")

      val table = make_table("running", List(name, worker_uuid, hostname, numa_node))
    }

    def read_running(db: SQL.Database): List[Job] =
      db.execute_query_statement(
        Running.table.select(sql = SQL.order_by(List(Running.name))),
        List.from[Job],
        { res =>
          val name = res.string(Running.name)
          val worker_uuid = res.string(Running.worker_uuid)
          val hostname = res.string(Running.hostname)
          val numa_node = res.get_int(Running.numa_node)
          Job(name, worker_uuid, Host.Node_Info(hostname, numa_node), None)
        }
      )

    def update_running(db: SQL.Database, running: State.Running): Boolean = {
      val running0 = read_running(db)
      val running1 = running.valuesIterator.map(_.no_build).toList

      val (delete, insert) = Library.symmetric_difference(running0, running1)

      if (delete.nonEmpty) {
        db.execute_statement(
          Running.table.delete(sql = SQL.where(Generic.sql(names = delete.map(_.name)))))
      }

      for (job <- insert) {
        db.execute_statement(Running.table.insert(), body =
          { stmt =>
            stmt.string(1) = job.name
            stmt.string(2) = job.worker_uuid
            stmt.string(3) = job.node_info.hostname
            stmt.int(4) = job.node_info.numa_node
          })
      }

      delete.nonEmpty || insert.nonEmpty
    }


    /* job results */

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

    def read_results_domain(db: SQL.Database): Set[String] =
      db.execute_query_statement(
        Results.table.select(List(Results.name)),
        Set.from[String], res => res.string(Results.name))

    def read_results(db: SQL.Database, names: List[String] = Nil): Map[String, Build_Job.Result] =
      db.execute_query_statement(
        Results.table.select(sql = if_proper(names, Results.name.where_member(names))),
        Map.from[String, Build_Job.Result],
        { res =>
          val name = res.string(Results.name)
          val hostname = res.string(Results.hostname)
          val numa_node = res.get_int(Results.numa_node)
          val rc = res.int(Results.rc)
          val out = res.string(Results.out)
          val err = res.string(Results.err)
          val timing =
            res.timing(
              Results.timing_elapsed,
              Results.timing_cpu,
              Results.timing_gc)
          val node_info = Host.Node_Info(hostname, numa_node)
          val process_result =
            Process_Result(rc,
              out_lines = split_lines(out),
              err_lines = split_lines(err),
              timing = timing)
          name -> Build_Job.Result(node_info, process_result)
        }
      )

    def update_results(db: SQL.Database, results: State.Results): Boolean = {
      val old_results = read_results_domain(db)
      val insert = results.iterator.filterNot(p => old_results.contains(p._1)).toList

      for ((name, result) <- insert) {
        val node_info = result.node_info
        val process_result = result.process_result
        db.execute_statement(Results.table.insert(), body =
          { stmt =>
            stmt.string(1) = name
            stmt.string(2) = node_info.hostname
            stmt.int(3) = node_info.numa_node
            stmt.int(4) = process_result.rc
            stmt.string(5) = cat_lines(process_result.out_lines)
            stmt.string(6) = cat_lines(process_result.err_lines)
            stmt.long(7) = process_result.timing.elapsed.ms
            stmt.long(8) = process_result.timing.cpu.ms
            stmt.long(9) = process_result.timing.gc.ms
          })
      }

      insert.nonEmpty
    }


    /* collective operations */

    val all_tables: SQL.Tables =
      SQL.Tables(
        Base.table,
        Workers.table,
        Progress.table,
        Sessions.table,
        Pending.table,
        Running.table,
        Results.table,
        Host.Data.Node_Info.table)

    def update_database(
      db: SQL.Database,
      worker_uuid: String,
      build_uuid: String,
      hostname: String,
      state: State
    ): State = {
      val changed =
        List(
          update_sessions(db, state.sessions),
          update_pending(db, state.pending),
          update_running(db, state.running),
          update_results(db, state.results),
          Host.Data.update_numa_next(db, hostname, state.numa_next))

      val serial0 = serial_max(db)
      val serial = if (changed.exists(identity)) State.inc_serial(serial0) else serial0

      stamp_worker(db, worker_uuid, serial)
      state.set_serial(serial).set_workers(read_workers(db))
    }
  }
}



/** main process **/

class Build_Process(
  protected final val build_context: Build_Process.Context,
  protected final val build_progress: Progress
)
extends AutoCloseable {
  /* context */

  protected final val store: Sessions.Store = build_context.store
  protected final val build_options: Options = store.options
  protected final val build_deps: Sessions.Deps = build_context.build_deps
  protected final val build_uuid: String = build_context.build_uuid
  protected final val worker_uuid: String = UUID.random().toString


  /* global state: internal var vs. external database */

  private var _state: Build_Process.State = init_state(Build_Process.State())

  private val _database: Option[SQL.Database] = store.open_build_database()

  def close(): Unit = synchronized { _database.foreach(_.close()) }

  protected def synchronized_database[A](body: => A): A =
    synchronized {
      _database match {
        case None => body
        case Some(db) => db.transaction_lock(Build_Process.Data.all_tables)(body)
      }
    }

  private def sync_database(): Unit =
    synchronized_database {
      for (db <- _database) {
        _state =
          Build_Process.Data.update_database(
            db, worker_uuid, build_uuid, build_context.hostname, _state)
      }
    }


  /* progress backed by database */

  private def progress_output(message: Progress.Message, build_progress_output: => Unit): Unit = {
    synchronized_database {
      val state1 = _state.inc_serial.progress_serial()
      for (db <- _database) {
        Build_Process.Data.write_progress(db, state1.serial, message, build_uuid)
        Build_Process.Data.stamp_worker(db, worker_uuid, state1.serial)
      }
      build_progress_output
      _state = state1
    }
  }

  protected object progress extends Progress {
    override def verbose: Boolean = build_progress.verbose

    override def output(message: Progress.Message): Unit =
      progress_output(message, if (do_output(message)) build_progress.output(message))

    override def theory(theory: Progress.Theory): Unit =
      progress_output(theory.message, build_progress.theory(theory))

    override def nodes_status(nodes_status: Document_Status.Nodes_Status): Unit =
      build_progress.nodes_status(nodes_status)

    override def stop(): Unit = build_progress.stop()
    override def stopped: Boolean = build_progress.stopped
  }

  protected val log: Logger = Logger.make_system_log(progress, build_options)


  /* policy operations */

  protected def init_state(state: Build_Process.State): Build_Process.State = {
    val sessions1 =
      build_context.sessions.foldLeft(state.sessions) { case (map, (name, session)) =>
        if (state.sessions.isDefinedAt(name)) map
        else map + (name -> session)
      }

    val old_pending = state.pending.iterator.map(_.name).toSet
    val new_pending =
      List.from(
        for {
          (name, session_context) <- build_context.sessions.iterator
          if !old_pending(name)
        } yield Build_Process.Task(name, session_context.deps))
    val pending1 = new_pending ::: state.pending

    state.copy(sessions = sessions1, pending = pending1)
  }

  protected def next_job(state: Build_Process.State): Option[String] =
    if (progress.stopped || state.running.size < build_context.max_jobs) {
      state.pending.filter(entry => entry.is_ready && !state.is_running(entry.name))
        .sortBy(_.name)(build_context.ordering)
        .headOption.map(_.name)
    }
    else None

  protected def start_session(state: Build_Process.State, session_name: String): Build_Process.State = {
    val ancestor_results =
      for (a <- build_context.sessions(session_name).ancestors) yield state.results(a)

    val input_shasum =
      if (ancestor_results.isEmpty) {
        SHA1.shasum_meta_info(SHA1.digest(Path.explode("$POLYML_EXE")))
      }
      else SHA1.flat_shasum(ancestor_results.map(_.output_shasum))

    val store_heap = build_context.store_heap(session_name)

    val (current, output_shasum) =
      store.check_output(session_name,
        sources_shasum = build_context.sources_shasum(session_name),
        input_shasum = input_shasum,
        fresh_build = build_context.fresh_build,
        store_heap = store_heap)

    val all_current = current && ancestor_results.forall(_.current)

    if (all_current) {
      state
        .remove_pending(session_name)
        .make_result(session_name, Process_Result.ok, output_shasum, current = true)
    }
    else if (build_context.no_build) {
      progress.echo("Skipping " + session_name + " ...", verbose = true)
      state.
        remove_pending(session_name).
        make_result(session_name, Process_Result.error, output_shasum)
    }
    else if (progress.stopped || !ancestor_results.forall(_.ok)) {
      progress.echo(session_name + " CANCELLED")
      state
        .remove_pending(session_name)
        .make_result(session_name, Process_Result.undefined, output_shasum)
    }
    else {
      val (numa_node, state1) = state.next_numa_node(build_context.numa_nodes)
      val node_info = Host.Node_Info(build_context.hostname, numa_node)

      progress.echo(
        (if (store_heap) "Building " else "Running ") + session_name +
          if_proper(node_info.numa_node, " on " + node_info) + " ...")

      store.init_output(session_name)

      val build =
        Build_Job.start_session(build_context, progress, log,
          build_deps.background(session_name), input_shasum, node_info)

      state1.add_running(Build_Process.Job(session_name, worker_uuid, node_info, Some(build)))
    }
  }


  /* build process roles */

  final def start_build(): Unit = synchronized_database {
    for (db <- _database) {
      Build_Process.Data.start_build(db, build_uuid, build_context.ml_platform,
        build_context.sessions_structure.session_prefs)
    }
  }

  final def stop_build(): Unit = synchronized_database {
    for (db <- _database) {
      Build_Process.Data.stop_build(db, build_uuid)
    }
  }

  final def start_worker(): Unit = synchronized_database {
    for (db <- _database) {
      val java = ProcessHandle.current()
      val java_pid = java.pid
      val java_start = Date.instant(java.info.startInstant.get)
      val serial =
        Build_Process.Data.start_worker(
          db, worker_uuid, build_uuid, build_context.hostname, java_pid, java_start)
      _state = _state.set_serial(serial)
    }
  }

  final def stop_worker(): Unit = synchronized_database {
    for (db <- _database) {
      Build_Process.Data.stamp_worker(db, worker_uuid, _state.serial, stop = true)
    }
  }


  /* run */

  def run(): Map[String, Process_Result] = {
    def finished(): Boolean = synchronized_database { _state.finished }

    def sleep(): Unit =
      Isabelle_Thread.interrupt_handler(_ => progress.stop()) {
        build_options.seconds("editor_input_delay").sleep()
      }

    def start_job(): Boolean = synchronized_database {
      next_job(_state) match {
        case Some(name) =>
          if (Build_Job.is_session_name(name)) {
            _state = start_session(_state, name)
            true
          }
          else error("Unsupported build job name " + quote(name))
        case None => false
      }
    }

    if (finished()) {
      progress.echo_warning("Nothing to build")
      Map.empty[String, Process_Result]
    }
    else {
      if (build_context.master) start_build()

      start_worker()
      if (build_context.master && !build_context.worker_active) {
        progress.echo("Waiting for external workers ...")
      }

      try {
        while (!finished()) {
          if (progress.stopped) synchronized_database { _state.stop_running() }

          for (build <- synchronized_database { _state.finished_running() }) {
            val job_name = build.job_name
            val (process_result, output_shasum) = build.join
            synchronized_database {
              _state = _state.
                remove_pending(job_name).
                remove_running(job_name).
                make_result(job_name, process_result, output_shasum, node_info = build.node_info)
            }
          }

          if (!start_job()) {
            sync_database()
            sleep()
          }
        }
      }
      finally {
        stop_worker()
        if (build_context.master) stop_build()
      }

      synchronized_database {
        for ((name, result) <- _state.results) yield name -> result.process_result
      }
    }
  }
}
