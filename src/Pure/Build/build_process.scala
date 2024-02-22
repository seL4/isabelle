/*  Title:      Pure/Build/build_process.scala
    Author:     Makarius

Build process for sessions, with build database, optional heap, and
optional presentation.
*/

package isabelle


import scala.collection.immutable.SortedMap
import scala.math.Ordering
import scala.annotation.tailrec


object Build_Process {
  /** state vs. database **/

  sealed case class Build(
    build_uuid: String,   // Database_Progress.context_uuid
    ml_platform: String,
    options: String,
    start: Date,
    stop: Option[Date],
    sessions: List[String]
  ) {
    def active: Boolean = stop.isEmpty

    def print: String =
      build_uuid + " (platform: " + ml_platform + ", start: " + Build_Log.print_date(start) +
        if_proper(stop, ", stop: " + Build_Log.print_date(stop.get)) + ")"
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
    start_date: Date,
    build: Option[Build_Job]
  ) extends Library.Named {
    def join_build: Option[Build_Job.Result] = build.flatMap(_.join)
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

    def defined(name: String): Boolean = graph.defined(name)
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

    def init(
      build_context: isabelle.Build.Context,
      database_server: Option[SQL.Database],
      progress: Progress = new Progress
    ): Sessions = {
      val sessions_structure = build_context.sessions_structure
      make(
        sessions_structure.build_graph.iterator.foldLeft(graph) {
          case (graph0, (name, (info, _))) =>
            val deps = info.parent.toList
            val prefs = info.session_prefs
            val ancestors = sessions_structure.build_requirements(deps)
            val sources_shasum = build_context.deps.sources_shasum(name)

            if (graph0.defined(name)) {
              val session0 = graph0.get_node(name)
              val prefs0 = session0.session_prefs
              val ancestors0 = session0.ancestors
              val sources_shasum0 = session0.sources_shasum

              def err(msg: String, a: String, b: String): Nothing =
                error("Conflicting dependencies for session " + quote(name) + ": " + msg + "\n" +
                  Library.indent_lines(2, a) + "\nvs.\n" + Library.indent_lines(2, b))

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
                err("sources disagree",
                  Library.trim_line(a.toString),
                  Library.trim_line(b.toString))
              }

              graph0
            }
            else {
              val session =
                Build_Job.Session_Context.load(database_server,
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
    def inc_serial: State = {
      require(serial < Long.MaxValue, "serial overflow")
      copy(serial = serial + 1)
    }

    def ready: State.Pending = pending.filter(_.is_ready)
    def next_ready: State.Pending = ready.filter(entry => !is_running(entry.name))

    def remove_pending(name: String): State =
      copy(pending = pending.flatMap(
        entry => if (entry.name == name) None else Some(entry.resolve(name))))

    def is_running(name: String): Boolean = running.isDefinedAt(name)

    def stop_running(): Unit =
      for (job <- running.valuesIterator; build <- job.build) build.cancel()

    def build_running: List[Build_Job] =
      List.from(for (job <- running.valuesIterator; build <- job.build) yield build)

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

    def ancestor_results(name: String): Option[List[Result]] = {
      val defined =
        sessions.defined(name) &&
        sessions(name).ancestors.forall(a => sessions.defined(a) && results.isDefinedAt(a))
      if (defined) Some(sessions(name).ancestors.map(results)) else None
    }
  }



  /** SQL data model **/

  object private_data extends SQL.Data("isabelle_build") {
    val database: Path = Path.explode("$ISABELLE_HOME_USER/build.db")

    def pull[A <: Library.Named](
      data_domain: Set[String],
      data_iterator: Set[String] => Iterator[A],
      old_data: Map[String, A]
    ): Map[String, A] = {
      val dom = data_domain -- old_data.keysIterator
      val data = old_data -- old_data.keysIterator.filterNot(data_domain)
      if (dom.isEmpty) data
      else data_iterator(dom).foldLeft(data) { case (map, a) => map + (a.name -> a) }
    }

    def pull0[A <: Library.Named](
      new_data: Map[String, A],
      old_data: Map[String, A]
    ): Map[String, A] = {
      pull(new_data.keySet, dom => new_data.valuesIterator.filter(a => dom(a.name)), old_data)
    }

    def pull1[A <: Library.Named](
      data_domain: Set[String],
      data_base: Set[String] => Map[String, A],
      old_data: Map[String, A]
    ): Map[String, A] = {
      pull(data_domain, dom => data_base(dom).valuesIterator, old_data)
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

      val table = make_table(List(build_uuid, ml_platform, options, start, stop))
    }

    def read_builds(db: SQL.Database): List[Build] = {
      val builds =
        db.execute_query_statement(Base.table.select(), List.from[Build],
          { res =>
            val build_uuid = res.string(Base.build_uuid)
            val ml_platform = res.string(Base.ml_platform)
            val options = res.string(Base.options)
            val start = res.date(Base.start)
            val stop = res.get_date(Base.stop)
            Build(build_uuid, ml_platform, options, start, stop, Nil)
          })

      for (build <- builds.sortBy(_.start)(Date.Ordering)) yield {
        val sessions = private_data.read_sessions_domain(db, build_uuid = build.build_uuid)
        build.copy(sessions = sessions.toList.sorted)
      }
    }

    def remove_builds(db: SQL.Database, remove: List[String]): Unit =
      if (remove.nonEmpty) {
        val sql = Generic.build_uuid.where_member(remove)
        db.execute_statement(SQL.MULTI(build_uuid_tables.map(_.delete(sql = sql))))
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
      val remove =
        db.execute_query_statement(
          Base.table.select(List(Base.build_uuid), sql = SQL.where(Base.stop.defined)),
          List.from[String], res => res.string(Base.build_uuid))

      remove_builds(db, remove)
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

      val table =
        make_table(
          List(name, deps, ancestors, options, sources, timeout,
            old_time, old_command_timings, build_uuid),
          name = "sessions")
    }

    def read_sessions_domain(db: SQL.Database, build_uuid: String = ""): Set[String] =
      db.execute_query_statement(
        Sessions.table.select(List(Sessions.name),
          sql = if_proper(build_uuid, Sessions.build_uuid.where_equal(build_uuid))),
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

    def update_sessions(
      db: SQL.Database,
      sessions: Build_Process.Sessions,
      old_sessions: Build_Process.Sessions
    ): Boolean = {
      val insert = sessions.iterator.filterNot(s => old_sessions.defined(s.name)).toList

      if (insert.nonEmpty) {
        db.execute_batch_statement(Sessions.table.insert(), batch =
          for (session <- insert) yield { (stmt: SQL.Statement) =>
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

      val table =
        make_table(List(worker_uuid, build_uuid, start, stamp, stop, serial), name = "workers")
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
      stop_now: Boolean = false
    ): Unit = {
      val sql = Workers.worker_uuid.where_equal(worker_uuid)

      val stop =
        db.execute_query_statementO(
          Workers.table.select(List(Workers.stop), sql = sql), _.get_date(Workers.stop)).flatten

      db.execute_statement(
        Workers.table.update(List(Workers.stamp, Workers.stop, Workers.serial), sql = sql),
        body = { stmt =>
          val now = db.now()
          stmt.date(1) = now
          stmt.date(2) = if (stop_now) Some(now) else stop
          stmt.long(3) = serial
        })
    }


    /* pending jobs */

    object Pending {
      val name = Generic.name.make_primary_key
      val deps = SQL.Column.string("deps")
      val info = SQL.Column.string("info")
      val build_uuid = Generic.build_uuid

      val table = make_table(List(name, deps, info, build_uuid), name = "pending")
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

    def update_pending(
      db: SQL.Database,
      pending: State.Pending,
      old_pending: State.Pending
    ): Boolean = {
      val (delete, insert) = Library.symmetric_difference(old_pending, pending)

      if (delete.nonEmpty) {
        db.execute_statement(
          Pending.table.delete(sql = Generic.sql_where(names = delete.map(_.name))))
      }

      if (insert.nonEmpty) {
        db.execute_batch_statement(Pending.table.insert(), batch =
          for (task <- insert) yield { (stmt: SQL.Statement) =>
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
      val rel_cpus = SQL.Column.string("rel_cpus")
      val start_date = SQL.Column.date("start_date")

      val table =
        make_table(
          List(name, worker_uuid, build_uuid, hostname, numa_node, rel_cpus, start_date),
          name = "running")
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
          val rel_cpus = res.string(Running.rel_cpus)
          val start_date = res.date(Running.start_date)

          val node_info = Host.Node_Info(hostname, numa_node, Host.Range.from(rel_cpus))
          name -> Job(name, worker_uuid, build_uuid, node_info, start_date, None)
        }
      )

    def update_running(
      db: SQL.Database,
      running: State.Running,
      old_running: State.Running
    ): Boolean = {
      val running0 = old_running.valuesIterator.toList
      val running1 = running.valuesIterator.toList
      val (delete, insert) = Library.symmetric_difference(running0, running1)

      if (delete.nonEmpty) {
        db.execute_statement(
          Running.table.delete(sql = Generic.sql_where(names = delete.map(_.name))))
      }

      if (insert.nonEmpty) {
        db.execute_batch_statement(Running.table.insert(), batch =
          for (job <- insert) yield { (stmt: SQL.Statement) =>
            stmt.string(1) = job.name
            stmt.string(2) = job.worker_uuid
            stmt.string(3) = job.build_uuid
            stmt.string(4) = job.node_info.hostname
            stmt.int(5) = job.node_info.numa_node
            stmt.string(6) = Host.Range(job.node_info.rel_cpus)
            stmt.date(7) = job.start_date
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
      val numa_node = SQL.Column.int("numa_node")
      val rel_cpus = SQL.Column.string("rel_cpus")
      val rc = SQL.Column.int("rc")
      val out = SQL.Column.string("out")
      val err = SQL.Column.string("err")
      val timing_elapsed = SQL.Column.long("timing_elapsed")
      val timing_cpu = SQL.Column.long("timing_cpu")
      val timing_gc = SQL.Column.long("timing_gc")
      val output_shasum = SQL.Column.string("output_shasum")
      val current = SQL.Column.bool("current")

      val table =
        make_table(
          List(name, worker_uuid, build_uuid, hostname, numa_node, rel_cpus,
            rc, out, err, timing_elapsed, timing_cpu, timing_gc, output_shasum, current),
          name = "results")
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
          val rel_cpus = res.string(Results.rel_cpus)
          val node_info = Host.Node_Info(hostname, numa_node, Host.Range.from(rel_cpus))

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

    def update_results(
      db: SQL.Database,
      results: State.Results,
      old_results: State.Results
    ): Boolean = {
      val insert =
        results.valuesIterator.filterNot(res => old_results.isDefinedAt(res.name)).toList

      if (insert.nonEmpty) {
        db.execute_batch_statement(Results.table.insert(), batch =
          for (result <- insert) yield { (stmt: SQL.Statement) =>
            val process_result = result.process_result
            stmt.string(1) = result.name
            stmt.string(2) = result.worker_uuid
            stmt.string(3) = result.build_uuid
            stmt.string(4) = result.node_info.hostname
            stmt.int(5) = result.node_info.numa_node
            stmt.string(6) = Host.Range(result.node_info.rel_cpus)
            stmt.int(7) = process_result.rc
            stmt.string(8) = cat_lines(process_result.out_lines)
            stmt.string(9) = cat_lines(process_result.err_lines)
            stmt.long(10) = process_result.timing.elapsed.ms
            stmt.long(11) = process_result.timing.cpu.ms
            stmt.long(12) = process_result.timing.gc.ms
            stmt.string(13) = result.output_shasum.toString
            stmt.bool(14) = result.current
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

    private val build_uuid_tables =
      tables.filter(table =>
        table.columns.exists(column => column.name == Generic.build_uuid.name))

    def pull_database(db: SQL.Database, worker_uuid: String, state: State): State = {
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
      state: State,
      old_state: State
    ): State = {
      val changed =
        List(
          update_sessions(db, state.sessions, old_state.sessions),
          update_pending(db, state.pending, old_state.pending),
          update_running(db, state.running, old_state.running),
          update_results(db, state.results, old_state.results))

      val state1 = if (changed.exists(identity)) state.inc_serial else state
      if (state1.serial != state.serial) stamp_worker(db, worker_uuid, state1.serial)

      state1
    }
  }

  def read_builds(db: SQL.Database): List[Build] =
    private_data.transaction_lock(db, create = true, label = "Build_Process.read_builds") {
      private_data.read_builds(db)
    }
}



/** main process **/

class Build_Process(
  protected final val build_context: Build.Context,
  protected final val build_progress: Progress,
  protected final val server: SSH.Server
)
extends AutoCloseable {
  /* context */

  protected final val store: Store = build_context.store
  protected final val build_options: Options = store.options
  protected final val build_deps: isabelle.Sessions.Deps = build_context.deps
  protected final val hostname: String = build_context.hostname
  protected final val build_uuid: String = build_context.build_uuid


  /* global resources with common close() operation */

  protected val _database_server: Option[SQL.Database] =
    try { store.maybe_open_database_server(server = server) }
    catch { case exn: Throwable => close(); throw exn }

  protected val _heaps_database: Option[SQL.Database] =
    try { store.maybe_open_heaps_database(_database_server, server = server) }
    catch { case exn: Throwable => close(); throw exn }

  protected val _build_database: Option[SQL.Database] =
    try {
      for (db <- store.maybe_open_build_database(server = server)) yield {
        if (!db.is_postgresql) {
          error("Distributed build requires PostgreSQL (option build_database_server)")
        }
        val store_tables = db.is_postgresql
        Build_Process.private_data.transaction_lock(db,
          create = true,
          label = "Build_Process.build_database"
        ) {
          Build_Process.private_data.clean_build(db)
          if (store_tables) Store.private_data.tables.lock(db, create = true)
        }
        if (build_context.master) {
          db.vacuum(Build_Process.private_data.tables.list)
          if (store_tables) db.vacuum(Store.private_data.tables.list)
        }
        db
      }
    }
    catch { case exn: Throwable => close(); throw exn }

  protected val build_delay: Time = {
    val option =
      _build_database match {
        case Some(db) if db.is_postgresql => "build_cluster_delay"
        case _ => "build_delay"
      }
    build_options.seconds(option)
  }

  protected val _host_database: SQL.Database =
    try { store.open_build_database(path = Host.private_data.database, server = server) }
    catch { case exn: Throwable => close(); throw exn }

  protected val (progress, worker_uuid) = synchronized {
    if (_build_database.isEmpty) (build_progress, UUID.random().toString)
    else {
      try {
        val db = store.open_build_database(Progress.private_data.database, server = server)
        val progress =
          new Database_Progress(db, build_progress,
            input_messages = build_context.master,
            output_stopped = build_context.master,
            hostname = hostname,
            context_uuid = build_uuid,
            kind = "build_process",
            timeout = Some(build_delay))
        (progress, progress.agent_uuid)
      }
      catch { case exn: Throwable => close(); throw exn }
    }
  }

  protected val log: Logger = Logger.make_system_log(progress, build_options)

  protected def open_build_cluster(): Build_Cluster =
    Build_Cluster.make(build_context, progress = build_progress).open()

  protected val _build_cluster: Build_Cluster =
    try {
      if (build_context.master && _build_database.isDefined) open_build_cluster()
      else Build_Cluster.none
    }
    catch { case exn: Throwable => close(); throw exn }

  def close(): Unit = synchronized {
    Option(_database_server).flatten.foreach(_.close())
    Option(_heaps_database).flatten.foreach(_.close())
    Option(_build_database).flatten.foreach(_.close())
    Option(_host_database).foreach(_.close())
    Option(_build_cluster).foreach(_.close())
    progress match {
      case db_progress: Database_Progress => db_progress.exit(close = true)
      case _ =>
    }
  }


  /* global state: internal var vs. external database */

  protected var _state: Build_Process.State = Build_Process.State()

  protected def synchronized_database[A](label: String)(body: => A): A =
    synchronized {
      _build_database match {
        case None => body
        case Some(db) =>
          Build_Process.private_data.transaction_lock(db, label = label) {
            val old_state = Build_Process.private_data.pull_database(db, worker_uuid, _state)
            _state = old_state
            val res = body
            _state = Build_Process.private_data.update_database(db, worker_uuid, _state, old_state)
            res
          }
      }
    }


  /* policy operations */

  protected def init_state(state: Build_Process.State): Build_Process.State = {
    val sessions1 = state.sessions.init(build_context, _database_server, progress = build_progress)

    val old_pending = state.pending.iterator.map(_.name).toSet
    val new_pending =
      List.from(
        for (session <- sessions1.iterator if !old_pending(session.name))
          yield Build_Process.Task(session.name, session.deps, JSON.Object.empty, build_uuid))
    val pending1 = new_pending ::: state.pending

    state.copy(sessions = sessions1, pending = pending1)
  }

  protected def next_jobs(state: Build_Process.State): List[String] = {
    val limit = {
      if (progress.stopped) { if (build_context.master) Int.MaxValue else 0 }
      else build_context.jobs - state.build_running.length
    }
    if (limit > 0) state.next_ready.sortBy(_.name)(state.sessions.ordering).take(limit).map(_.name)
    else Nil
  }

  protected def next_node_info(state: Build_Process.State, session_name: String): Host.Node_Info = {
    def used_nodes: Set[Int] =
      Set.from(for (job <- state.running.valuesIterator; i <- job.node_info.numa_node) yield i)
    val numa_node = Host.next_numa_node(_host_database, hostname, state.numa_nodes, used_nodes)
    Host.Node_Info(hostname, numa_node, Nil)
  }

  protected def start_session(
    state: Build_Process.State,
    session_name: String,
    ancestor_results: List[Build_Process.Result]
  ): Build_Process.State = {
    val sources_shasum = state.sessions(session_name).sources_shasum

    val input_shasum =
      if (ancestor_results.isEmpty) ML_Process.bootstrap_shasum()
      else SHA1.flat_shasum(ancestor_results.map(_.output_shasum))

    val store_heap =
      build_context.build_heap || Sessions.is_pure(session_name) ||
      state.sessions.iterator.exists(_.ancestors.contains(session_name))

    val (current, output_shasum) =
      store.check_output(_database_server, session_name,
        session_options = build_context.sessions_structure(session_name).options,
        sources_shasum = sources_shasum,
        input_shasum = input_shasum,
        fresh_build = build_context.fresh_build,
        store_heap = store_heap)

    val finished = current && ancestor_results.forall(_.current)
    val skipped = build_context.no_build
    val cancelled = progress.stopped || !ancestor_results.forall(_.ok)

    if (!skipped && !cancelled) {
      for (db <- _database_server orElse _heaps_database) {
        val hierarchy =
          (session_name :: ancestor_results.map(_.name))
            .map(store.output_session(_, store_heap = true))
        ML_Heap.restore(db, hierarchy, cache = store.cache.compress)
      }
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
      if (build_context.master) {
        progress.echo(session_name + " CANCELLED")
        state
          .remove_pending(session_name)
          .make_result(result_name, Process_Result.undefined, output_shasum)
      }
      else state
    }
    else {
      val node_info = next_node_info(state, session_name)

      val print_node_info =
        node_info.numa_node.isDefined || node_info.rel_cpus.nonEmpty  ||
        _build_database.isDefined && _build_database.get.is_postgresql

      progress.echo(
        (if (store_heap) "Building " else "Running ") + session_name +
          (if (print_node_info) " (on " + node_info + ")" else "") + " ...")

      val session = state.sessions(session_name)

      val build =
        Build_Job.start_session(build_context, session, progress, log, server,
          build_deps.background(session_name), sources_shasum, input_shasum, node_info, store_heap)

      val job =
        Build_Process.Job(session_name, worker_uuid, build_uuid, node_info, Date.now(), Some(build))

      state.add_running(job)
    }
  }


  /* build process roles */

  final def is_session_name(job_name: String): Boolean =
    !Long_Name.is_qualified(job_name)

  protected final def start_build(): Unit = synchronized_database("Build_Process.start_build") {
    for (db <- _build_database) {
      Build_Process.private_data.start_build(db, build_uuid, build_context.ml_platform,
        build_context.sessions_structure.session_prefs)
    }
  }

  protected final def stop_build(): Unit = synchronized_database("Build_Process.stop_build") {
    for (db <- _build_database) {
      Build_Process.private_data.stop_build(db, build_uuid)
    }
  }

  protected final def start_worker(): Unit = synchronized_database("Build_Process.start_worker") {
    for (db <- _build_database) {
      _state = _state.inc_serial
      Build_Process.private_data.start_worker(db, worker_uuid, build_uuid, _state.serial)
    }
  }

  protected final def stop_worker(): Unit = synchronized_database("Build_Process.stop_worker") {
    for (db <- _build_database) {
      Build_Process.private_data.stamp_worker(db, worker_uuid, _state.serial, stop_now = true)
    }
  }


  /* run */

  def run(): Build.Results = {
    synchronized_database("Build_Process.init") {
      if (build_context.master) {
        _build_cluster.init()
        _state = init_state(_state)
      }
      _state = _state.copy(numa_nodes = Host.numa_nodes(enabled = build_context.numa_shuffling))
    }

    def finished(): Boolean = synchronized_database("Build_Process.test") {
      if (!build_context.master && progress.stopped) _state.build_running.isEmpty
      else _state.pending.isEmpty
    }

    def sleep(): Unit =
      Isabelle_Thread.interrupt_handler(_ => progress.stop()) { build_delay.sleep() }

    val build_progress_warnings = Synchronized(Set.empty[String])
    def build_progress_warning(msg: String): Unit =
      build_progress_warnings.change(seen =>
        if (seen(msg)) seen else { build_progress.echo_warning(msg); seen + msg })

    def check_jobs(): Boolean = synchronized_database("Build_Process.check_jobs") {
      val jobs = next_jobs(_state)
      for (name <- jobs) {
        if (is_session_name(name)) {
          if (build_context.sessions_structure.defined(name)) {
            _state.ancestor_results(name) match {
              case Some(results) => _state = start_session(_state, name, results)
              case None =>
                build_progress_warning("Bad build job " + quote(name) + ": no ancestor results")
            }
          }
          else build_progress_warning("Bad build job " + quote(name) + ": no session info")
        }
        else build_progress_warning("Bad build job " + quote(name))
      }
      jobs.nonEmpty
    }

    if (finished()) {
      progress.echo_warning("Nothing to build")
      Build.Results(build_context)
    }
    else {
      if (build_context.master) start_build()
      start_worker()
      _build_cluster.start()

      if (build_context.master && !build_context.worker && _build_cluster.active()) {
        build_progress.echo("Waiting for external workers ...")
      }

      try {
        while (!finished()) {
          synchronized_database("Build_Process.main") {
            if (progress.stopped) _state.stop_running()

            for (job <- _state.finished_running()) {
              job.join_build match {
                case None =>
                  _state = _state.remove_running(job.name)
                case Some(result) =>
                  val result_name = (job.name, worker_uuid, build_uuid)
                  _state = _state.
                    remove_pending(job.name).
                    remove_running(job.name).
                    make_result(result_name,
                      result.process_result,
                      result.output_shasum,
                      node_info = job.node_info)
              }
            }
          }

          if (!check_jobs()) sleep()
        }
      }
      finally {
        _build_cluster.stop()
        stop_worker()
        if (build_context.master) stop_build()
      }

      synchronized_database("Build_Process.result") {
        val results = for ((name, result) <- _state.results) yield name -> result.process_result
        Build.Results(build_context, results = results, other_rc = _build_cluster.rc)
      }
    }
  }


  /* snapshot */

  def snapshot(): Build_Process.Snapshot = synchronized_database("Build_Process.snapshot") {
    val (builds, workers) =
      _build_database match {
        case None => (Nil, Nil)
        case Some(db) =>
          (Build_Process.private_data.read_builds(db),
           Build_Process.private_data.read_workers(db))
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
