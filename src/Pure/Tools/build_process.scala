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

  sealed case class Context(
    store: Store,
    build_deps: isabelle.Sessions.Deps,
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
      "Build_Process.Context(build_uuid = " + quote(build_uuid) +
        if_proper(master, ", master = true") + ")"

    def build_options: Options = store.options

    def sessions_structure: isabelle.Sessions.Structure = build_deps.sessions_structure

    def worker_active: Boolean = max_jobs > 0
  }



  /** dynamic state **/

  sealed case class Build(
    build_uuid: String,   // Database_Progress.context_uuid
    ml_platform: String,
    options: String,
    start: Date,
    stop: Option[Date],
    sessions: List[String]
  ) {
    def active: Boolean = stop.isEmpty
  }

  sealed case class Worker(
    worker_uuid: String,  // Database_Progress.agent_uuid
    build_uuid: String,
    start: Date,
    stamp: Date,
    stop: Option[Date],
    serial: Long
  )

  sealed case class Task(
    name: String,
    deps: List[String],
    info: JSON.Object.T,
    build_uuid: String
  ) {
    def is_ready: Boolean = deps.isEmpty
    def resolve(dep: String): Task =
      if (deps.contains(dep)) copy(deps = deps.filterNot(_ == dep)) else this
  }

  sealed case class Job(
    name: String,
    worker_uuid: String,
    build_uuid: String,
    node_info: Host.Node_Info,
    build: Option[Build_Job]
  ) extends Library.Named {
    def no_build: Job = copy(build = None)
  }

  sealed case class Result(
    name: String,
    worker_uuid: String,
    build_uuid: String,
    node_info: Host.Node_Info,
    process_result: Process_Result,
    output_shasum: SHA1.Shasum,
    current: Boolean
  ) extends Library.Named {
    def ok: Boolean = process_result.ok
  }

  object Sessions {
    type Graph = isabelle.Graph[String, Build_Job.Session_Context]
    val empty: Sessions = new Sessions(Graph.string)
  }

  final class Sessions private(val graph: Sessions.Graph) {
    override def toString: String = graph.toString

    def apply(name: String): Build_Job.Session_Context = graph.get_node(name)

    def iterator: Iterator[Build_Job.Session_Context] =
      for (name <- graph.topological_order.iterator) yield apply(name)

    def make(new_graph: Sessions.Graph): Sessions =
      if (graph == new_graph) this
      else {
        new Sessions(
          new_graph.iterator.foldLeft(new_graph) {
            case (g, (name, (session, _))) => g.add_deps_acyclic(name, session.deps)
          })
      }

    def pull(
      data_domain: Set[String],
      data: Set[String] => List[Build_Job.Session_Context]
    ): Sessions = {
      val dom = data_domain -- iterator.map(_.name)
      make(data(dom).foldLeft(graph.restrict(dom)) { case (g, e) => g.new_node(e.name, e) })
    }

    def init(build_context: Context, progress: Progress = new Progress): Sessions = {
      val sessions_structure = build_context.sessions_structure
      make(
        sessions_structure.build_graph.iterator.foldLeft(graph) {
          case (graph0, (name, (info, _))) =>
            val deps = info.parent.toList
            val prefs = info.session_prefs
            val ancestors = sessions_structure.build_requirements(deps)
            val sources_shasum = build_context.build_deps.sources_shasum(name)

            if (graph0.defined(name)) {
              val session0 = graph0.get_node(name)
              val prefs0 = session0.session_prefs
              val ancestors0 = session0.ancestors
              val sources_shasum0 = session0.sources_shasum

              def err(msg: String, a: String, b: String): Nothing =
                error("Conflicting dependencies for session " + quote(name) + ": " +
                  msg + "\n" + a + "\nvs.\n" + b)

              if (prefs0 != prefs) {
                err("preferences disagree",
                  Symbol.cartouche_decoded(prefs0), Symbol.cartouche_decoded(prefs))
              }
              if (ancestors0 != ancestors) {
                err("ancestors disagree", commas_quote(ancestors0), commas_quote(ancestors))
              }
              if (sources_shasum0 != sources_shasum) {
                val a = sources_shasum0 - sources_shasum
                val b = sources_shasum - sources_shasum0
                err("sources disagree", a.toString, b.toString)
              }

              graph0
            }
            else {
              val session =
                Build_Job.Session_Context.load(
                  build_context.build_uuid, name, deps, ancestors, prefs, sources_shasum,
                  info.timeout, build_context.store, progress = progress)
              graph0.new_node(name, session)
            }
        }
      )
    }

    lazy val max_time: Map[String, Double] = {
      val maximals = graph.maximals.toSet
      def descendants_time(name: String): Double = {
        if (maximals.contains(name)) apply(name).old_time.seconds
        else {
          val descendants = graph.all_succs(List(name)).toSet
          val g = graph.restrict(descendants)
          (0.0 :: g.maximals.flatMap { desc =>
            val ps = g.all_preds(List(desc))
            if (ps.exists(p => !graph.defined(p))) None
            else Some(ps.map(p => apply(p).old_time.seconds).sum)
          }).max
        }
      }
      Map.from(
        for (name <- graph.keys_iterator)
        yield name -> descendants_time(name)).withDefaultValue(0.0)
    }

    lazy val ordering: Ordering[String] =
      (a: String, b: String) =>
        max_time(b) compare max_time(a) match {
          case 0 =>
            apply(b).timeout compare apply(a).timeout match {
              case 0 => a compare b
              case ord => ord
            }
          case ord => ord
        }
  }

  sealed case class Snapshot(
    builds: List[Build],        // available build configurations
    workers: List[Worker],      // available worker processes
    sessions: Sessions,         // static build targets
    pending: State.Pending,     // dynamic build "queue"
    running: State.Running,     // presently running jobs
    results: State.Results)     // finished results

  object State {
    type Pending = List[Task]
    type Running = Map[String, Job]
    type Results = Map[String, Result]

    def inc_serial(serial: Long): Long = {
      require(serial < Long.MaxValue, "serial overflow")
      serial + 1
    }
  }

  sealed case class State(
    serial: Long = 0,
    numa_nodes: List[Int] = Nil,
    sessions: Sessions = Sessions.empty,
    pending: State.Pending = Nil,
    running: State.Running = Map.empty,
    results: State.Results = Map.empty
  ) {
    require(serial >= 0, "serial underflow")
    def inc_serial: State = copy(serial = State.inc_serial(serial))
    def set_serial(i: Long): State = {
      require(serial <= i, "non-monotonic change of serial")
      copy(serial = i)
    }

    def finished: Boolean = pending.isEmpty

    def remove_pending(name: String): State =
      copy(pending = pending.flatMap(
        entry => if (entry.name == name) None else Some(entry.resolve(name))))

    def is_running(name: String): Boolean = running.isDefinedAt(name)

    def stop_running(): Unit =
      for (job <- running.valuesIterator; build <- job.build) build.cancel()

    def finished_running(): List[Job] =
      List.from(
        for (job <- running.valuesIterator; build <- job.build if build.is_finished)
        yield job)

    def add_running(job: Job): State =
      copy(running = running + (job.name -> job))

    def remove_running(name: String): State =
      copy(running = running - name)

    def make_result(
      result_name: (String, String, String),
      process_result: Process_Result,
      output_shasum: SHA1.Shasum,
      node_info: Host.Node_Info = Host.Node_Info.none,
      current: Boolean = false
    ): State = {
      val (name, worker_uuid, build_uuid) = result_name
      val result =
        Result(name, worker_uuid, build_uuid, node_info, process_result, output_shasum, current)
      copy(results = results + (name -> result))
    }
  }



  /** SQL data model **/

  object Data extends SQL.Data("isabelle_build") {
    val database: Path = Path.explode("$ISABELLE_HOME_USER/build.db")

    def pull_data[A <: Library.Named](
      data_domain: Set[String],
      data_iterator: Set[String] => Iterator[A],
      old_data: Map[String, A]
    ): Map[String, A] = {
      val dom = data_domain -- old_data.keysIterator
      val data = old_data -- old_data.keysIterator.filterNot(dom)
      if (dom.isEmpty) data
      else data_iterator(dom).foldLeft(data) { case (map, a) => map + (a.name -> a) }
    }

    def pull0[A <: Library.Named](
      new_data: Map[String, A],
      old_data: Map[String, A]
    ): Map[String, A] = {
      pull_data(new_data.keySet, dom => new_data.valuesIterator.filter(a => dom(a.name)), old_data)
    }

    def pull1[A <: Library.Named](
      data_domain: Set[String],
      data_base: Set[String] => Map[String, A],
      old_data: Map[String, A]
    ): Map[String, A] = {
      pull_data(data_domain, dom => data_base(dom).valuesIterator, old_data)
    }

    object Generic {
      val build_uuid = SQL.Column.string("build_uuid")
      val worker_uuid = SQL.Column.string("worker_uuid")
      val name = SQL.Column.string("name")

      def sql(
        build_uuid: String = "",
        worker_uuid: String = "",
        names: Iterable[String] = Nil
      ): SQL.Source =
        SQL.and(
          if_proper(build_uuid, Generic.build_uuid.equal(build_uuid)),
          if_proper(worker_uuid, Generic.worker_uuid.equal(worker_uuid)),
          if_proper(names, Generic.name.member(names)))

      def sql_where(
        build_uuid: String = "",
        worker_uuid: String = "",
        names: Iterable[String] = Nil
      ): SQL.Source = {
        SQL.where(sql(build_uuid = build_uuid, worker_uuid = worker_uuid, names = names))
      }
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

    def read_builds(db: SQL.Database, build_uuid: String = ""): List[Build] = {
      val builds =
        db.execute_query_statement(
          Base.table.select(sql = Generic.sql_where(build_uuid = build_uuid)),
          List.from[Build],
          { res =>
            val build_uuid = res.string(Base.build_uuid)
            val ml_platform = res.string(Base.ml_platform)
            val options = res.string(Base.options)
            val start = res.date(Base.start)
            val stop = res.get_date(Base.stop)
            Build(build_uuid, ml_platform, options, start, stop, Nil)
          })

      for (build <- builds.sortBy(_.start)(Date.Ordering)) yield {
        val sessions = Data.read_sessions_domain(db, build_uuid = build.build_uuid)
        build.copy(sessions = sessions.toList.sorted)
      }
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
        Base.table.update(List(Base.stop), sql = Base.build_uuid.where_equal(build_uuid)),
        body = { stmt => stmt.date(1) = db.now() })

    def clean_build(db: SQL.Database): Unit = {
      val old =
        db.execute_query_statement(
          Base.table.select(List(Base.build_uuid), sql = SQL.where(Base.stop.defined)),
          List.from[String], res => res.string(Base.build_uuid))

      if (old.nonEmpty) {
        for (table <- build_uuid_tables) {
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

    def read_sessions_domain(db: SQL.Database, build_uuid: String = ""): Set[String] =
      db.execute_query_statement(
        Sessions.table.select(List(Sessions.name),
          sql = if_proper(build_uuid, Sessions.name.where_equal(build_uuid))),
        Set.from[String], res => res.string(Sessions.name))

    def read_sessions(db: SQL.Database,
      names: Iterable[String] = Nil,
      build_uuid: String = ""
    ): List[Build_Job.Session_Context] = {
      db.execute_query_statement(
        Sessions.table.select(
          sql =
            SQL.where_and(
              if_proper(names, Sessions.name.member(names)),
              if_proper(build_uuid, Sessions.build_uuid.equal(build_uuid)))
        ),
        List.from[Build_Job.Session_Context],
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
          Build_Job.Session_Context(name, deps, ancestors, options, sources_shasum,
            timeout, old_time, old_command_timings_blob, build_uuid)
        }
      )
    }

    def update_sessions(db: SQL.Database, sessions: Build_Process.Sessions): Boolean = {
      val old_sessions = read_sessions_domain(db)
      val insert = sessions.iterator.filterNot(s => old_sessions.contains(s.name)).toList

      for (session <- insert) {
        db.execute_statement(Sessions.table.insert(), body =
          { stmt =>
            stmt.string(1) = session.name
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


    /* workers */

    object Workers {
      val worker_uuid = Generic.worker_uuid.make_primary_key
      val build_uuid = Generic.build_uuid
      val start = SQL.Column.date("start")
      val stamp = SQL.Column.date("stamp")
      val stop = SQL.Column.date("stop")
      val serial = SQL.Column.long("serial")

      val table = make_table("workers", List(worker_uuid, build_uuid, start, stamp, stop, serial))
    }

    def read_serial(db: SQL.Database): Long =
      db.execute_query_statementO[Long](
        Workers.table.select(List(Workers.serial.max)), _.long(Workers.serial)).getOrElse(0L)

    def read_workers(
      db: SQL.Database,
      build_uuid: String = "",
      worker_uuid: String = ""
    ): List[Worker] = {
      db.execute_query_statement(
        Workers.table.select(
          sql = Generic.sql_where(build_uuid = build_uuid, worker_uuid = worker_uuid)),
          List.from[Worker],
          { res =>
            Worker(
              worker_uuid = res.string(Workers.worker_uuid),
              build_uuid = res.string(Workers.build_uuid),
              start = res.date(Workers.start),
              stamp = res.date(Workers.stamp),
              stop = res.get_date(Workers.stop),
              serial = res.long(Workers.serial))
          })
    }

    def start_worker(
      db: SQL.Database,
      worker_uuid: String,
      build_uuid: String,
      serial: Long
    ): Unit = {
      def err(msg: String): Nothing =
        error("Cannot start worker " + worker_uuid + if_proper(msg, "\n" + msg))

      val build_stop =
        db.execute_query_statementO(
          Base.table.select(List(Base.stop), sql = Base.build_uuid.where_equal(build_uuid)),
          res => res.get_date(Base.stop))

      build_stop match {
        case Some(None) =>
        case Some(Some(_)) => err("for already stopped build process " + build_uuid)
        case None => err("for unknown build process " + build_uuid)
      }

      db.execute_statement(Workers.table.insert(), body =
        { stmt =>
          val now = db.now()
          stmt.string(1) = worker_uuid
          stmt.string(2) = build_uuid
          stmt.date(3) = now
          stmt.date(4) = now
          stmt.date(5) = None
          stmt.long(6) = serial
        })
    }

    def stamp_worker(
      db: SQL.Database,
      worker_uuid: String,
      serial: Long,
      stop: Boolean = false
    ): Unit = {
      val sql =

      db.execute_statement(
        Workers.table.update(List(Workers.stamp, Workers.stop, Workers.serial),
          sql = Workers.worker_uuid.where_equal(worker_uuid)),
        body = { stmt =>
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
      val build_uuid = Generic.build_uuid

      val table = make_table("pending", List(name, deps, info, build_uuid))
    }

    def read_pending(db: SQL.Database): List[Task] =
      db.execute_query_statement(
        Pending.table.select(sql = SQL.order_by(List(Pending.name))),
        List.from[Task],
        { res =>
          val name = res.string(Pending.name)
          val deps = res.string(Pending.deps)
          val info = res.string(Pending.info)
          val build_uuid = res.string(Pending.build_uuid)
          Task(name, split_lines(deps), JSON.Object.parse(info), build_uuid)
        })

    def update_pending(db: SQL.Database, pending: State.Pending): Boolean = {
      val old_pending = read_pending(db)
      val (delete, insert) = Library.symmetric_difference(old_pending, pending)

      if (delete.nonEmpty) {
        db.execute_statement(
          Pending.table.delete(sql = Generic.sql_where(names = delete.map(_.name))))
      }

      for (task <- insert) {
        db.execute_statement(Pending.table.insert(), body =
          { stmt =>
            stmt.string(1) = task.name
            stmt.string(2) = cat_lines(task.deps)
            stmt.string(3) = JSON.Format(task.info)
            stmt.string(4) = task.build_uuid
          })
      }

      delete.nonEmpty || insert.nonEmpty
    }


    /* running jobs */

    object Running {
      val name = Generic.name.make_primary_key
      val worker_uuid = Generic.worker_uuid
      val build_uuid = Generic.build_uuid
      val hostname = SQL.Column.string("hostname")
      val numa_node = SQL.Column.int("numa_node")

      val table = make_table("running", List(name, worker_uuid, build_uuid, hostname, numa_node))
    }

    def read_running(db: SQL.Database): State.Running =
      db.execute_query_statement(
        Running.table.select(sql = SQL.order_by(List(Running.name))),
        Map.from[String, Job],
        { res =>
          val name = res.string(Running.name)
          val worker_uuid = res.string(Running.worker_uuid)
          val build_uuid = res.string(Running.build_uuid)
          val hostname = res.string(Running.hostname)
          val numa_node = res.get_int(Running.numa_node)
          name -> Job(name, worker_uuid, build_uuid, Host.Node_Info(hostname, numa_node), None)
        }
      )

    def update_running(db: SQL.Database, running: State.Running): Boolean = {
      val running0 = read_running(db).valuesIterator.toList
      val running1 = running.valuesIterator.map(_.no_build).toList

      val (delete, insert) = Library.symmetric_difference(running0, running1)

      if (delete.nonEmpty) {
        db.execute_statement(
          Running.table.delete(sql = Generic.sql_where(names = delete.map(_.name))))
      }

      for (job <- insert) {
        db.execute_statement(Running.table.insert(), body =
          { stmt =>
            stmt.string(1) = job.name
            stmt.string(2) = job.worker_uuid
            stmt.string(3) = job.build_uuid
            stmt.string(4) = job.node_info.hostname
            stmt.int(5) = job.node_info.numa_node
          })
      }

      delete.nonEmpty || insert.nonEmpty
    }


    /* job results */

    object Results {
      val name = Generic.name.make_primary_key
      val worker_uuid = Generic.worker_uuid
      val build_uuid = Generic.build_uuid
      val hostname = SQL.Column.string("hostname")
      val numa_node = SQL.Column.string("numa_node")
      val rc = SQL.Column.int("rc")
      val out = SQL.Column.string("out")
      val err = SQL.Column.string("err")
      val timing_elapsed = SQL.Column.long("timing_elapsed")
      val timing_cpu = SQL.Column.long("timing_cpu")
      val timing_gc = SQL.Column.long("timing_gc")
      val output_shasum = SQL.Column.string("output_shasum")
      val current = SQL.Column.bool("current")

      val table =
        make_table("results",
          List(name, worker_uuid, build_uuid, hostname, numa_node,
            rc, out, err, timing_elapsed, timing_cpu, timing_gc, output_shasum, current))
    }

    def read_results_domain(db: SQL.Database): Set[String] =
      db.execute_query_statement(
        Results.table.select(List(Results.name)),
        Set.from[String], res => res.string(Results.name))

    def read_results(db: SQL.Database, names: Iterable[String] = Nil): State.Results =
      db.execute_query_statement(
        Results.table.select(sql = if_proper(names, Results.name.where_member(names))),
        Map.from[String, Result],
        { res =>
          val name = res.string(Results.name)
          val worker_uuid = res.string(Results.worker_uuid)
          val build_uuid = res.string(Results.build_uuid)
          val hostname = res.string(Results.hostname)
          val numa_node = res.get_int(Results.numa_node)
          val node_info = Host.Node_Info(hostname, numa_node)

          val rc = res.int(Results.rc)
          val out = res.string(Results.out)
          val err = res.string(Results.err)
          val timing =
            res.timing(
              Results.timing_elapsed,
              Results.timing_cpu,
              Results.timing_gc)
          val process_result =
            Process_Result(rc,
              out_lines = split_lines(out),
              err_lines = split_lines(err),
              timing = timing)

          val output_shasum = SHA1.fake_shasum(res.string(Results.output_shasum))
          val current = res.bool(Results.current)

          name ->
            Result(name, worker_uuid, build_uuid, node_info, process_result, output_shasum, current)
        }
      )

    def update_results(db: SQL.Database, results: State.Results): Boolean = {
      val old_results = read_results_domain(db)
      val insert = results.valuesIterator.filterNot(res => old_results.contains(res.name)).toList

      for (result <- insert) {
        val process_result = result.process_result
        db.execute_statement(Results.table.insert(), body =
          { stmt =>
            stmt.string(1) = result.name
            stmt.string(2) = result.worker_uuid
            stmt.string(3) = result.build_uuid
            stmt.string(4) = result.node_info.hostname
            stmt.int(5) = result.node_info.numa_node
            stmt.int(6) = process_result.rc
            stmt.string(7) = cat_lines(process_result.out_lines)
            stmt.string(8) = cat_lines(process_result.err_lines)
            stmt.long(9) = process_result.timing.elapsed.ms
            stmt.long(10) = process_result.timing.cpu.ms
            stmt.long(11) = process_result.timing.gc.ms
            stmt.string(12) = result.output_shasum.toString
            stmt.bool(13) = result.current
          })
      }

      insert.nonEmpty
    }


    /* collective operations */

    override val tables =
      SQL.Tables(
        Base.table,
        Workers.table,
        Sessions.table,
        Pending.table,
        Running.table,
        Results.table)

    val build_uuid_tables =
      tables.filter(table =>
        table.columns.exists(column => column.name == Generic.build_uuid.name))

    def pull_database(
      db: SQL.Database,
      worker_uuid: String,
      hostname: String,
      state: State
    ): State = {
      val serial_db = read_serial(db)
      if (serial_db == state.serial) state
      else {
        val serial = serial_db max state.serial
        stamp_worker(db, worker_uuid, serial)

        val sessions = state.sessions.pull(read_sessions_domain(db), read_sessions(db, _))
        val pending = read_pending(db)
        val running = pull0(read_running(db), state.running)
        val results = pull1(read_results_domain(db), read_results(db, _), state.results)

        state.copy(serial = serial, sessions = sessions, pending = pending,
          running = running, results = results)
      }
    }

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
          update_results(db, state.results))

      val serial0 = state.serial
      val serial = if (changed.exists(identity)) State.inc_serial(serial0) else serial0

      stamp_worker(db, worker_uuid, serial)
      state.set_serial(serial)
    }
  }

  def read_builds(db: SQL.Database): List[Build] =
    Data.transaction_lock(db, create = true) { Data.read_builds(db) }
}



/** main process **/

class Build_Process(
  protected final val build_context: Build_Process.Context,
  protected final val build_progress: Progress
)
extends AutoCloseable {
  /* context */

  protected final val store: Store = build_context.store
  protected final val build_options: Options = store.options
  protected final val build_deps: isabelle.Sessions.Deps = build_context.build_deps
  protected final val hostname: String = build_context.hostname
  protected final val build_uuid: String = build_context.build_uuid


  /* progress backed by database */

  private val _database_server: Option[SQL.Database] =
    try { store.maybe_open_database_server() }
    catch { case exn: Throwable => close(); throw exn }

  private val _build_database: Option[SQL.Database] =
    try {
      for (db <- store.maybe_open_build_database()) yield {
        val shared_db = db.is_postgresql
        Build_Process.Data.transaction_lock(db, create = true) {
          Build_Process.Data.clean_build(db)
          if (shared_db) Store.Data.tables.lock(db, create = true)
        }
        Build_Process.Data.vacuum(db,
          more_tables = if (shared_db) Store.Data.tables else SQL.Tables.empty)
        db
      }
    }
    catch { case exn: Throwable => close(); throw exn }

  private val _host_database: Option[SQL.Database] =
    try { store.maybe_open_build_database(path = Host.Data.database) }
    catch { case exn: Throwable => close(); throw exn }

  protected val (progress, worker_uuid) = synchronized {
    _build_database match {
      case None => (build_progress, UUID.random().toString)
      case Some(db) =>
        try {
          val progress_db = store.open_build_database(Progress.Data.database)
          val progress =
            new Database_Progress(progress_db, build_progress,
              hostname = hostname,
              context_uuid = build_uuid,
              kind = "build_process")
          (progress, progress.agent_uuid)
        }
        catch { case exn: Throwable => close(); throw exn }
    }
  }

  protected val log: Logger = Logger.make_system_log(progress, build_options)

  def close(): Unit = synchronized {
    Option(_database_server).flatten.foreach(_.close())
    Option(_build_database).flatten.foreach(_.close())
    Option(_host_database).flatten.foreach(_.close())
    progress match {
      case db_progress: Database_Progress =>
        db_progress.exit(close = true)
      case _ =>
    }
  }

  /* global state: internal var vs. external database */

  private var _state: Build_Process.State = Build_Process.State()

  protected def synchronized_database[A](body: => A): A = synchronized {
    _build_database match {
      case None => body
      case Some(db) =>
        Build_Process.Data.transaction_lock(db) {
          progress.asInstanceOf[Database_Progress].sync()
          _state = Build_Process.Data.pull_database(db, worker_uuid, hostname, _state)
          val res = body
          _state =
            Build_Process.Data.update_database(db, worker_uuid, build_uuid, hostname, _state)
          res
        }
    }
  }


  /* policy operations */

  protected def init_state(state: Build_Process.State): Build_Process.State = {
    val sessions1 = state.sessions.init(build_context, progress = build_progress)

    val old_pending = state.pending.iterator.map(_.name).toSet
    val new_pending =
      List.from(
        for (session <- sessions1.iterator if !old_pending(session.name))
          yield Build_Process.Task(session.name, session.deps, JSON.Object.empty, build_uuid))
    val pending1 = new_pending ::: state.pending

    state.copy(
      numa_nodes = Host.numa_nodes(enabled = build_context.numa_shuffling),
      sessions = sessions1,
      pending = pending1)
  }

  protected def next_job(state: Build_Process.State): Option[String] =
    if (progress.stopped || state.running.size < build_context.max_jobs) {
      state.pending.filter(entry => entry.is_ready && !state.is_running(entry.name))
        .sortBy(_.name)(state.sessions.ordering)
        .headOption.map(_.name)
    }
    else None

  protected def start_session(state: Build_Process.State, session_name: String): Build_Process.State = {
    val ancestor_results =
      for (a <- state.sessions(session_name).ancestors) yield state.results(a)

    val sources_shasum = state.sessions(session_name).sources_shasum

    val input_shasum =
      if (ancestor_results.isEmpty) ML_Process.bootstrap_shasum()
      else SHA1.flat_shasum(ancestor_results.map(_.output_shasum))

    val store_heap =
      build_context.build_heap || Sessions.is_pure(session_name) ||
      state.sessions.iterator.exists(_.ancestors.contains(session_name))

    val (current, output_shasum) =
      store.check_output(session_name,
        session_options = build_context.sessions_structure(session_name).options,
        sources_shasum = sources_shasum,
        input_shasum = input_shasum,
        fresh_build = build_context.fresh_build,
        store_heap = store_heap)

    val finished = current && ancestor_results.forall(_.current)
    val skipped = build_context.no_build
    val cancelled = progress.stopped || !ancestor_results.forall(_.ok)

    if (!skipped && !cancelled) {
      ML_Heap.restore(_database_server, session_name, store.output_heap(session_name),
        cache = store.cache.compress)
    }

    val result_name = (session_name, worker_uuid, build_uuid)

    if (finished) {
      state
        .remove_pending(session_name)
        .make_result(result_name, Process_Result.ok, output_shasum, current = true)
    }
    else if (skipped) {
      progress.echo("Skipping " + session_name + " ...", verbose = true)
      state.
        remove_pending(session_name).
        make_result(result_name, Process_Result.error, output_shasum)
    }
    else if (cancelled) {
      progress.echo(session_name + " CANCELLED")
      state
        .remove_pending(session_name)
        .make_result(result_name, Process_Result.undefined, output_shasum)
    }
    else {
      def used_nodes: Set[Int] =
        Set.from(for (job <- state.running.valuesIterator; i <- job.node_info.numa_node) yield i)
      val numa_node =
        for {
          db <- _host_database
          n <- Host.next_numa_node(db, hostname, state.numa_nodes, used_nodes)
        } yield n
      val node_info = Host.Node_Info(hostname, numa_node)

      progress.echo(
        (if (store_heap) "Building " else "Running ") + session_name +
          if_proper(node_info.numa_node, " on " + node_info) + " ...")

      store.clean_output(_database_server, session_name, session_init = true)

      val session = state.sessions(session_name)

      val build =
        Build_Job.start_session(build_context, session, progress, log, _database_server,
          build_deps.background(session_name), sources_shasum, input_shasum, node_info, store_heap)

      val job = Build_Process.Job(session_name, worker_uuid, build_uuid, node_info, Some(build))

      state.add_running(job)
    }
  }


  /* build process roles */

  final def is_session_name(job_name: String): Boolean =
    !Long_Name.is_qualified(job_name)

  protected final def start_build(): Unit = synchronized_database {
    for (db <- _build_database) {
      Build_Process.Data.start_build(db, build_uuid, build_context.ml_platform,
        build_context.sessions_structure.session_prefs)
    }
  }

  protected final def stop_build(): Unit = synchronized_database {
    for (db <- _build_database) {
      Build_Process.Data.stop_build(db, build_uuid)
    }
  }

  protected final def start_worker(): Unit = synchronized_database {
    for (db <- _build_database) {
      _state = _state.inc_serial
      Build_Process.Data.start_worker(db, worker_uuid, build_uuid, _state.serial)
    }
  }

  protected final def stop_worker(): Unit = synchronized_database {
    for (db <- _build_database) {
      Build_Process.Data.stamp_worker(db, worker_uuid, _state.serial, stop = true)
    }
  }


  /* run */

  def run(): Map[String, Process_Result] = {
    if (build_context.master) synchronized_database { _state = init_state(_state) }

    def finished(): Boolean = synchronized_database { _state.finished }

    def sleep(): Unit =
      Isabelle_Thread.interrupt_handler(_ => progress.stop()) {
        build_options.seconds("editor_input_delay").sleep()
      }

    def start_job(): Boolean = synchronized_database {
      next_job(_state) match {
        case Some(name) =>
          if (is_session_name(name)) {
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
          synchronized_database {
            if (progress.stopped) _state.stop_running()

            for (job <- _state.finished_running()) {
              val result_name = (job.name, worker_uuid, build_uuid)
              val (process_result, output_shasum) = job.build.get.join
              _state = _state.
                remove_pending(job.name).
                remove_running(job.name).
                make_result(result_name, process_result, output_shasum, node_info = job.node_info)
            }
          }

          if (!start_job()) sleep()
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


  /* snapshot */

  def snapshot(): Build_Process.Snapshot = synchronized_database {
    val (builds, workers) =
      _build_database match {
        case None => (Nil, Nil)
        case Some(db) =>
          (Build_Process.Data.read_builds(db),
           Build_Process.Data.read_workers(db))
      }
    Build_Process.Snapshot(
      builds = builds,
      workers = workers,
      sessions = _state.sessions,
      pending = _state.pending,
      running = _state.running,
      results = _state.results)
  }


  /* toString */

  override def toString: String =
    "Build_Process(worker_uuid = " + quote(worker_uuid) + ", build_uuid = " + quote(build_uuid) +
      if_proper(build_context.master, ", master = true") + ")"
}
