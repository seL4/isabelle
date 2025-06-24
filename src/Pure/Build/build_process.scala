/*  Title:      Pure/Build/build_process.scala
    Author:     Makarius

Build process for sessions, with build database, optional heap, and
optional presentation.
*/

package isabelle


import scala.math.Ordering


object Build_Process {
  /** state vs. database **/

  sealed case class Build(
    build_uuid: String,   // Database_Progress.context_uuid
    build_id: Long,
    ml_platform: String,
    options: String,
    start: Date,
    stop: Option[Date],
    sessions: List[String]
  ) {
    def active: Boolean = stop.isEmpty
    def active_build_uuid: Option[String] = if (active) Some(build_uuid) else None

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

  object Task {
    type Entry = (String, Task)
    def entry(session: Build_Job.Session_Context, build_context: isabelle.Build.Context): Entry =
      session.name -> Task(session.name, session.deps, build_context.build_uuid)
  }

  sealed case class Task(
    name: String,
    deps: List[String],
    build_uuid: String
  ) extends Name.T {
    def is_ready: Boolean = deps.isEmpty
    def resolve(dep: String): Option[Task] =
      if (deps.contains(dep)) Some(copy(deps = deps.filterNot(_ == dep))) else None
  }

  sealed case class Job(
    name: String,
    worker_uuid: String,
    build_uuid: String,
    node_info: Host.Node_Info,
    start_date: Date,
    build: Option[Build_Job]
  ) extends Name.T

  sealed case class Result(
    name: String,
    worker_uuid: String,
    build_uuid: String,
    node_info: Host.Node_Info,
    start_date: Date,
    process_result: Process_Result,
    output_shasum: SHA1.Shasum,
    current: Boolean
  ) extends Name.T {
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

    def store_heap(name: String): Boolean =
      isabelle.Sessions.is_pure(name) || iterator.exists(_.ancestors.contains(name))

    def data: Name.Data[Build_Job.Session_Context] =
      Map.from(for ((_, (session, _)) <- graph.iterator) yield session.name -> session)

    def make(new_graph: Sessions.Graph): Sessions =
      if (graph == new_graph) this
      else {
        new Sessions(
          new_graph.iterator.foldLeft(new_graph) {
            case (g, (name, (session, _))) => g.add_deps_acyclic(name, session.deps)
          })
      }

    def update(updates: List[Update.Op[Build_Job.Session_Context]]): Sessions = {
      val graph1 =
        updates.foldLeft(graph) {
          case (g, Update.Delete(name)) => g.del_node(name)
          case (g, Update.Insert(session)) =>
            (if (g.defined(session.name)) g.del_node(session.name) else g)
              .new_node(session.name, session)
        }
      make(graph1)
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
    def inc_serial(serial: Long): Long = {
      require(serial < Long.MaxValue, "serial overflow")
      serial + 1
    }

    type Pending = Name.Data[Task]
    type Running = Name.Data[Job]
    type Results = Name.Data[Result]
  }

  sealed case class State(
    serial: Long = 0,
    sessions: Sessions = Sessions.empty,
    pending: State.Pending = Map.empty,
    running: State.Running = Map.empty,
    results: State.Results = Map.empty
  ) {
    def next_serial: Long = State.inc_serial(serial)

    def ready: List[Task] = pending.valuesIterator.filter(_.is_ready).toList.sortBy(_.name)
    def next_ready: List[Task] = ready.filter(task => !is_running(task.name))
    def exists_ready: Boolean =
      pending.valuesIterator.exists(task => task.is_ready && !is_running(task.name))

    def remove_pending(a: String): State =
      copy(pending =
        pending.foldLeft(pending) {
          case (map, (b, task)) =>
            if (a == b) map - a
            else {
              task.resolve(a) match {
                case None => map
                case Some(task1) => map + (b -> task1)
              }
            }
        })

    def is_running(name: String): Boolean = running.isDefinedAt(name)

    def build_running: List[Build_Job] =
      running.valuesIterator.flatMap(_.build).toList

    def finished_running(): Boolean =
      build_running.exists(_.is_finished)

    def busy_running(jobs: Int): Boolean =
      jobs <= 0 || jobs <= build_running.length

    def add_running(job: Job): State =
      copy(running = running + (job.name -> job))

    def remove_running(name: String): State =
      copy(running = running - name)

    def make_result(
      result_name: (String, String, String),
      process_result: Process_Result,
      output_shasum: SHA1.Shasum,
      start_date: Date,
      node_info: Host.Node_Info = Host.Node_Info.none,
      current: Boolean = false
    ): State = {
      val (name, worker_uuid, build_uuid) = result_name
      val result =
        Result(name, worker_uuid, build_uuid, node_info, start_date, process_result, output_shasum,
          current)
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


    /* tables */

    override lazy val tables: SQL.Tables =
      SQL.Tables(
        Updates.table,
        Sessions.table,
        Pending.table,
        Running.table,
        Results.table,
        Base.table,
        Workers.table)

    private lazy val build_uuid_tables = tables.filter(Generic.build_uuid_table)
    private lazy val build_id_tables =
      tables.filter(t => Generic.build_id_table(t) && !Generic.build_uuid_table(t))


    /* notifications */

    lazy val channel: String = Base.table.name
    lazy val channel_ready: SQL.Notification = SQL.Notification(channel, payload = "ready")


    /* generic columns */

    object Generic {
      val build_id = SQL.Column.long("build_id")
      val build_uuid = SQL.Column.string("build_uuid")
      val worker_uuid = SQL.Column.string("worker_uuid")
      val name = SQL.Column.string("name")

      def build_id_table(table: SQL.Table): Boolean =
        table.columns.exists(_.equals_name(build_id))

      def build_uuid_table(table: SQL.Table): Boolean =
        table.columns.exists(_.equals_name(build_uuid))

      def sql(
        build_id: Long = 0,
        build_uuid: String = "",
        worker_uuid: String = "",
        names: Iterable[String] = Nil
      ): SQL.Source =
        SQL.and(
          if_proper(build_id > 0, Generic.build_id.equal(build_id)),
          if_proper(build_uuid, Generic.build_uuid.equal(build_uuid)),
          if_proper(worker_uuid, Generic.worker_uuid.equal(worker_uuid)),
          if_proper(names, Generic.name.member(names)))

      def sql_where(
        build_id: Long = 0,
        build_uuid: String = "",
        worker_uuid: String = "",
        names: Iterable[String] = Nil
      ): SQL.Source = {
        SQL.where(sql(
          build_id = build_id,
          build_uuid = build_uuid,
          worker_uuid = worker_uuid,
          names = names))
      }
    }


    /* recorded updates */

    object Updates {
      val build_id = Generic.build_id.make_primary_key
      val serial = SQL.Column.long("serial").make_primary_key
      val kind = SQL.Column.int("kind").make_primary_key
      val name = Generic.name.make_primary_key

      val table = make_table(List(build_id, serial, kind, name), name = "updates")

      // virtual columns for JOIN with data
      val delete = SQL.Column.bool("delete").make_expr(name.undefined)
      val dom = SQL.Column.string("dom")
      val dom_name = dom.make_expr(name.ident)
      val name_dom = name.make_expr(dom.ident)
    }

    def read_updates[A](
      db: SQL.Database,
      table: SQL.Table,
      build_id: Long,
      serial_seen: Long,
      get: SQL.Result => A
    ): List[Update.Op[A]] = {
      val domain_columns = List(Updates.dom_name)
      val domain_table =
        SQL.Table("domain", domain_columns, body =
          Updates.table.select(domain_columns, distinct = true, sql =
            SQL.where_and(
              Updates.build_id.equal(build_id),
              Updates.serial.ident + " > " + serial_seen,
              Updates.kind.equal(tables.index(table)))))

      val select_columns =
        Updates.delete :: Updates.name_dom :: table.columns.filterNot(_.equals_name(Generic.name))
      val select_sql =
        SQL.select(select_columns, sql =
          domain_table.query_named + SQL.join_outer + table +
            " ON " + Updates.dom + " = " + Generic.name)

      db.execute_query_statement(select_sql, List.from[Update.Op[A]],
        res =>
          if (res.bool(Updates.delete)) Update.Delete(res.string(Updates.name))
          else Update.Insert(get(res)))
    }

    def write_updates(
      db: SQL.Database,
      build_id: Long,
      serial: Long,
      updates: List[Update]
    ): Unit =
      db.execute_batch_statement(db.insert_permissive(Updates.table), batch =
        for (update <- updates.iterator; kind = update.kind; name <- update.domain.iterator)
        yield { (stmt: SQL.Statement) =>
          require(build_id > 0 && serial > 0 && kind > 0 && name.nonEmpty,
            "Bad database update: build_id = " + build_id + ", serial = " + serial +
              ", kind = " + kind + ", name = " + quote(name))
          stmt.long(1) = build_id
          stmt.long(2) = serial
          stmt.int(3) = kind
          stmt.string(4) = name
        })


    /* base table */

    object Base {
      val build_uuid = Generic.build_uuid.make_primary_key
      val build_id = Generic.build_id.make_primary_key
      val ml_platform = SQL.Column.string("ml_platform")
      val options = SQL.Column.string("options")
      val start = SQL.Column.date("start")
      val stop = SQL.Column.date("stop")

      val table = make_table(List(build_uuid, build_id, ml_platform, options, start, stop))
    }

    def read_build_ids(db: SQL.Database, build_uuids: List[String]): List[Long] =
      db.execute_query_statement(
        Base.table.select(List(Base.build_id),
          sql = if_proper(build_uuids, Base.build_uuid.where_member(build_uuids))),
        List.from[Long], res => res.long(Base.build_id))

    def get_build_id(db: SQL.Database, build_uuid: String): Long = {
      read_build_ids(db, build_uuids = List(build_uuid)) match {
        case build_id :: _ => build_id
        case _ =>
          db.execute_query_statementO(
            Base.table.select(List(Base.build_id.max)), _.long(Base.build_id)).getOrElse(0L) + 1L
      }
    }

    def read_builds(db: SQL.Database): List[Build] = {
      val builds =
        db.execute_query_statement(Base.table.select(), List.from[Build],
          { res =>
            val build_uuid = res.string(Base.build_uuid)
            val build_id = res.long(Base.build_id)
            val ml_platform = res.string(Base.ml_platform)
            val options = res.string(Base.options)
            val start = res.date(Base.start)
            val stop = res.get_date(Base.stop)
            Build(build_uuid, build_id, ml_platform, options, start, stop, Nil)
          })

      for (build <- builds.sortBy(_.start)(Date.Ordering)) yield {
        build.copy(sessions = private_data.read_sessions(db, build_uuid = build.build_uuid).sorted)
      }
    }

    def remove_builds(db: SQL.Database, build_uuids: List[String]): Unit =
      if (build_uuids.nonEmpty) {
        val build_ids = read_build_ids(db, build_uuids = build_uuids)

        val sql1 = Generic.build_uuid.where_member(build_uuids)
        val sql2 = Generic.build_id.where_member_long(build_ids)
        db.execute_statement(
          SQL.MULTI(
            build_uuid_tables.map(_.delete(sql = sql1)) ++
            build_id_tables.map(_.delete(sql = sql2))))
      }

    def start_build(
      db: SQL.Database,
      build_id: Long,
      build_uuid: String,
      ml_platform: String,
      options: String,
      start: Date
    ): Unit = {
      db.execute_statement(Base.table.insert(), body =
        { stmt =>
          stmt.string(1) = build_uuid
          stmt.long(2) = build_id
          stmt.string(3) = ml_platform
          stmt.string(4) = options
          stmt.date(5) = start
          stmt.date(6) = None
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

      lazy val table_index: Int = tables.index(table)
    }

    def read_sessions(db: SQL.Database, build_uuid: String = ""): List[String] =
      db.execute_query_statement(
        Sessions.table.select(List(Sessions.name),
          sql = if_proper(build_uuid, Sessions.build_uuid.where_equal(build_uuid))),
        List.from[String], res => res.string(Sessions.name))

    def pull_sessions(db: SQL.Database, build_id: Long, state: State): Sessions =
      state.sessions.update(
        read_updates(db, Sessions.table, build_id, state.serial,
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
          })
      )

    def update_sessions(
      db: SQL.Database,
      sessions: Build_Process.Sessions,
      old_sessions: Build_Process.Sessions
    ): Update = {
      val update =
        if (old_sessions.eq(sessions)) Update.empty
        else Update.make(old_sessions.data, sessions.data, kind = Sessions.table_index)

      if (update.deletes) {
        db.execute_statement(
          Sessions.table.delete(sql = Generic.sql_where(names = update.delete)))
      }

      if (update.inserts) {
        db.execute_batch_statement(Sessions.table.insert(), batch =
          for (name <- update.insert) yield { (stmt: SQL.Statement) =>
            val session = sessions(name)
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

      update
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

      lazy val table_index: Int = tables.index(table)
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
      val build_uuid = Generic.build_uuid

      val table = make_table(List(name, deps, build_uuid), name = "pending")

      lazy val table_index: Int = tables.index(table)
    }

    def pull_pending(db: SQL.Database, build_id: Long, state: State): State.Pending =
      Update.data(state.pending,
        read_updates(db, Pending.table, build_id, state.serial,
          { res =>
            val name = res.string(Pending.name)
            val deps = res.string(Pending.deps)
            val build_uuid = res.string(Pending.build_uuid)
            Task(name, split_lines(deps), build_uuid)
        })
      )

    def update_pending(
      db: SQL.Database,
      pending: State.Pending,
      old_pending: State.Pending
    ): Update = {
      val update = Update.make(old_pending, pending, kind = Pending.table_index)

      if (update.deletes) {
        db.execute_statement(
          Pending.table.delete(sql = Generic.sql_where(names = update.delete)))
      }

      if (update.inserts) {
        db.execute_batch_statement(Pending.table.insert(), batch =
          for (name <- update.insert) yield { (stmt: SQL.Statement) =>
            val task = pending(name)
            stmt.string(1) = task.name
            stmt.string(2) = cat_lines(task.deps)
            stmt.string(3) = task.build_uuid
          })
      }

      update
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

      lazy val table_index: Int = tables.index(table)
    }

    def pull_running(db: SQL.Database, build_id: Long, state: State): State.Running =
      Update.data(state.running,
        read_updates(db, Running.table, build_id, state.serial,
          { res =>
            val name = res.string(Running.name)
            val worker_uuid = res.string(Running.worker_uuid)
            val build_uuid = res.string(Running.build_uuid)
            val hostname = res.string(Running.hostname)
            val numa_node = res.get_int(Running.numa_node)
            val rel_cpus = res.string(Running.rel_cpus)
            val start_date = res.date(Running.start_date)
            val node_info = Host.Node_Info(hostname, numa_node, Host.Range.from(rel_cpus))

            Job(name, worker_uuid, build_uuid, node_info, start_date, None)
          })
      )

    def update_running(
      db: SQL.Database,
      running: State.Running,
      old_running: State.Running
    ): Update = {
      val update = Update.make(old_running, running, kind = Running.table_index)

      if (update.deletes) {
        db.execute_statement(
          Running.table.delete(sql = Generic.sql_where(names = update.delete)))
      }

      if (update.inserts) {
        db.execute_batch_statement(Running.table.insert(), batch =
          for (name <- update.insert) yield { (stmt: SQL.Statement) =>
            val job = running(name)
            stmt.string(1) = job.name
            stmt.string(2) = job.worker_uuid
            stmt.string(3) = job.build_uuid
            stmt.string(4) = job.node_info.hostname
            stmt.int(5) = job.node_info.numa_node
            stmt.string(6) = Host.Range(job.node_info.rel_cpus)
            stmt.date(7) = job.start_date
          })
      }

      update
    }


    /* job results */

    object Results {
      val name = Generic.name.make_primary_key
      val worker_uuid = Generic.worker_uuid
      val build_uuid = Generic.build_uuid
      val hostname = SQL.Column.string("hostname")
      val numa_node = SQL.Column.int("numa_node")
      val rel_cpus = SQL.Column.string("rel_cpus")
      val start_date = SQL.Column.date("start_date")
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
          List(name, worker_uuid, build_uuid, hostname, numa_node, rel_cpus, start_date,
            rc, out, err, timing_elapsed, timing_cpu, timing_gc, output_shasum, current),
          name = "results")

      lazy val table_index: Int = tables.index(table)
    }

    def pull_results(db: SQL.Database, build_id: Long, state: State): State.Results =
      Update.data(state.results,
        read_updates(db, Results.table, build_id, state.serial,
          { res =>
            val name = res.string(Results.name)
            val worker_uuid = res.string(Results.worker_uuid)
            val build_uuid = res.string(Results.build_uuid)
            val hostname = res.string(Results.hostname)
            val numa_node = res.get_int(Results.numa_node)
            val rel_cpus = res.string(Results.rel_cpus)
            val node_info = Host.Node_Info(hostname, numa_node, Host.Range.from(rel_cpus))

            val start_date = res.date(Results.start_date)

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

            Result(name, worker_uuid, build_uuid, node_info, start_date, process_result,
              output_shasum, current)
          })
      )

    def update_results(
      db: SQL.Database,
      results: State.Results,
      old_results: State.Results
    ): Update = {
      val update = Update.make(old_results, results, kind = Results.table_index)

      if (update.deletes) {
        db.execute_statement(
          Results.table.delete(sql = Generic.sql_where(names = update.delete)))
      }

      if (update.inserts) {
        db.execute_batch_statement(Results.table.insert(), batch =
          for (name <- update.insert) yield { (stmt: SQL.Statement) =>
            val result = results(name)
            val process_result = result.process_result
            stmt.string(1) = result.name
            stmt.string(2) = result.worker_uuid
            stmt.string(3) = result.build_uuid
            stmt.string(4) = result.node_info.hostname
            stmt.int(5) = result.node_info.numa_node
            stmt.string(6) = Host.Range(result.node_info.rel_cpus)
            stmt.date(7) = result.start_date
            stmt.int(8) = process_result.rc
            stmt.string(9) = cat_lines(process_result.out_lines)
            stmt.string(10) = cat_lines(process_result.err_lines)
            stmt.long(11) = process_result.timing.elapsed.ms
            stmt.long(12) = process_result.timing.cpu.ms
            stmt.long(13) = process_result.timing.gc.ms
            stmt.string(14) = result.output_shasum.toString
            stmt.bool(15) = result.current
          })
      }

      update
    }


    /* collective operations */

    def pull_state(db: SQL.Database, build_id: Long, worker_uuid: String, state: State): State = {
      val serial_db = read_serial(db)
      if (serial_db == state.serial) state
      else {
        val serial = serial_db max state.serial
        stamp_worker(db, worker_uuid, serial)

        val sessions = pull_sessions(db, build_id, state)
        val pending = pull_pending(db, build_id, state)
        val running = pull_running(db, build_id, state)
        val results = pull_results(db, build_id, state)

        state.copy(serial = serial, sessions = sessions, pending = pending,
          running = running, results = results)
      }
    }

    def push_state(
      db: SQL.Database,
      build_id: Long,
      worker_uuid: String,
      state: State,
      old_state: State
    ): State = {
      val updates =
        List(
          update_sessions(db, state.sessions, old_state.sessions),
          update_pending(db, state.pending, old_state.pending),
          update_running(db, state.running, old_state.running),
          update_results(db, state.results, old_state.results)
        ).filter(_.defined)

      if (updates.nonEmpty) {
        val serial = state.next_serial
        write_updates(db, build_id, serial, updates)
        stamp_worker(db, worker_uuid, serial)
        state.copy(serial = serial)
      }
      else state
    }
  }

  def read_builds(db: SQL.Database): List[Build] =
    private_data.transaction_lock(db, create = true, label = "Build_Process.read_builds") {
      private_data.read_builds(db)
    }

  def init_build(
    db: SQL.Database,
    build_context: isabelle.Build.Context,
    build_start: Date
  ): Long =
    private_data.transaction_lock(db, create = true, label = "Build_Process.init_build") {
      db.listen(private_data.channel)
      val build_uuid = build_context.build_uuid
      val build_id = private_data.get_build_id(db, build_uuid)
      if (build_context.master) {
        private_data.start_build(db, build_id, build_uuid, build_context.ml_platform,
          build_context.sessions_structure.session_prefs, build_start)
      }
      build_id
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

  private var warning_seen = Set.empty[String]
  protected def warning(msg: String): Unit = synchronized {
    if (!warning_seen(msg)) {
      build_progress.echo_warning(msg)
      warning_seen += msg
    }
  }


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

  protected def build_receive(filter: SQL.Notification => Boolean): List[SQL.Notification] =
    _build_database.flatMap(_.receive(filter)).getOrElse(Nil)

  protected def build_send(notification: SQL.Notification): Unit =
    _build_database.foreach(_.send(notification))

  protected def build_cluster: Boolean =
    _build_database match {
      case Some(db) => db.is_postgresql
      case None => false
    }

  protected val build_delay: Time =
    build_options.seconds(
      if (!build_cluster) "build_delay"
      else if (build_context.master) "build_delay_master"
      else "build_delay_worker")

  protected val build_expire: Int =
    if (!build_cluster || build_context.master) 1
    else build_options.int("build_cluster_expire").max(1)

  protected val _host_database: SQL.Database =
    try { store.open_build_database(path = Host.private_data.database, server = server) }
    catch { case exn: Throwable => close(); throw exn }

  protected val (progress, worker_uuid) = synchronized {
    if (_build_database.isEmpty) (build_progress, UUID.random_string())
    else {
      try {
        val db = store.open_build_database(Database_Progress.private_data.database, server = server)
        val progress =
          new Database_Progress(db, build_progress,
            input_messages = build_context.master,
            hostname = hostname,
            context_uuid = build_uuid,
            kind = "build_process",
            timeout = Some(build_delay),
            tick_expire = build_expire)
        (progress, progress.agent_uuid)
      }
      catch { case exn: Throwable => close(); throw exn }
    }
  }

  protected val log: Logger = Logger.make_system_log(progress, build_options)

  protected val build_start: Date = build_context.build_start getOrElse progress.now()

  protected val build_id: Long =
    _build_database match {
      case None => 0L
      case Some(db) => Build_Process.init_build(db, build_context, build_start)
    }

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
      case db_progress: Database_Progress => db_progress.close()
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
            val old_state =
              Build_Process.private_data.pull_state(db, build_id, worker_uuid, _state)
            _state = old_state
            val res = body
            _state =
              Build_Process.private_data.push_state(
                db, build_id, worker_uuid, _state, old_state)
            res
          }
      }
    }


  /* policy operations */

  protected def next_jobs(state: Build_Process.State): List[String] = {
    val limit = {
      if (progress.stopped) { if (build_context.master) Int.MaxValue else 0 }
      else build_context.jobs - state.build_running.length
    }
    if (limit > 0) state.next_ready.sortBy(_.name)(state.sessions.ordering).take(limit).map(_.name)
    else Nil
  }

  protected def next_node_info(state: Build_Process.State, session_name: String): Host.Node_Info = {
    val available_nodes = build_context.numa_nodes
    val used_nodes =
      Set.from(for (job <- state.running.valuesIterator; i <- job.node_info.numa_node) yield i)
    val numa_node = Host.next_numa_node(_host_database, hostname, available_nodes, used_nodes)
    Host.Node_Info(hostname, numa_node, Nil)
  }

  protected def start_session(
    state: Build_Process.State,
    session_name: String,
    ancestor_results: List[Build_Process.Result]
  ): Build_Process.State = {
    val sources_shasum = state.sessions(session_name).sources_shasum
    val input_shasum = store.make_shasum(ancestor_results.map(_.output_shasum))
    val store_heap = build_context.store_heap || state.sessions.store_heap(session_name)
    val (current, output_shasum) =
      store.check_output(_database_server, session_name,
        sources_shasum = sources_shasum,
        input_shasum = input_shasum,
        build_thorough = build_context.sessions_structure(session_name).build_thorough,
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

    val start = progress.now()

    if (finished) {
      state
        .remove_pending(session_name)
        .make_result(result_name, Process_Result.ok, output_shasum, start, current = true)
    }
    else if (skipped) {
      progress.echo("Skipping " + session_name + " ...", verbose = true)
      state.
        remove_pending(session_name).
        make_result(result_name, Process_Result.error, output_shasum, start)
    }
    else if (cancelled) {
      progress.echo(session_name + " CANCELLED")
      state
        .remove_pending(session_name)
        .make_result(result_name, Process_Result.undefined, output_shasum, start)
    }
    else {
      val build_log_verbose = build_options.bool("build_log_verbose")

      val start_time = start - build_start
      val start_time_msg = build_log_verbose

      val node_info = next_node_info(state, session_name)
      val node_info_msg = node_info.numa || build_log_verbose

      progress.echo(
        (if (store_heap) "Building " else "Running ") + session_name +
          if_proper(start_time_msg || node_info_msg,
            " (" +
              if_proper(start_time_msg, "started " + start_time.message_hms) +
              if_proper(start_time_msg && node_info_msg, " ") +
              if_proper(node_info_msg, "on " + node_info.toString) +
            ")") + " ...")

      val session = state.sessions(session_name)
      val background = build_deps.background(session_name)

      val build =
        Build_Job.start_session(build_context, session, progress, log, server,
          background, sources_shasum, input_shasum, node_info, store_heap)

      state.add_running(
        Build_Process.Job(session_name, worker_uuid, build_uuid, node_info, start, Some(build)))
    }
  }


  /* build process roles */

  final def is_session_name(job_name: String): Boolean =
    !Long_Name.is_qualified(job_name)

  protected final def stop_build(): Unit = synchronized_database("Build_Process.stop_build") {
    for (db <- _build_database) {
      Build_Process.private_data.stop_build(db, build_uuid)
    }
  }

  protected final def start_worker(): Unit = synchronized_database("Build_Process.start_worker") {
    for (db <- _build_database) {
      _state = _state.copy(serial = _state.next_serial)
      Build_Process.private_data.start_worker(db, worker_uuid, build_uuid, _state.serial)
    }
  }

  protected final def stop_worker(): Unit = synchronized_database("Build_Process.stop_worker") {
    for (db <- _build_database) {
      Build_Process.private_data.stamp_worker(db, worker_uuid, _state.serial, stop_now = true)
    }
  }


  /* prepare */

  def prepare(): Unit = {
    for (name <- build_context.clean_sessions) {
      store.clean_output(_database_server orElse _heaps_database, name, progress = progress)
    }
  }


  /* run */

  protected def finished(): Boolean = synchronized {
    if (!build_context.master && progress.stopped) _state.build_running.isEmpty
    else _state.pending.isEmpty
  }

  private var _build_tick: Long = 0L

  protected def build_action(): Boolean =
    Isabelle_Thread.interrupt_handler(_ => progress.stop()) {
      val received = build_receive(n => n.channel == Build_Process.private_data.channel)
      val ready = received.contains(Build_Process.private_data.channel_ready)
      val reactive = ready && synchronized { !_state.busy_running(build_context.jobs) }

      val finished = synchronized { _state.finished_running() }

      def sleep: Boolean = {
        build_delay.sleep()
        val expired = synchronized { _build_tick += 1; _build_tick % build_expire == 0 }
        expired || reactive || progress.stopped
      }

      finished || sleep
    }

  protected def init_unsynchronized(): Unit =
    if (build_context.master) {
      val sessions1 =
        _state.sessions.init(build_context, _database_server, progress = build_progress)
      val pending1 =
        sessions1.iterator.foldLeft(_state.pending) {
          case (map, session) =>
            if (map.isDefinedAt(session.name)) map
            else map + Build_Process.Task.entry(session, build_context)
        }
      _state = _state.copy(sessions = sessions1, pending = pending1)
    }

  protected def main_unsynchronized(): Unit = {
    for (job <- _state.running.valuesIterator; build <- job.build if build.is_finished) {
      val result = build.join
      val result_name = (job.name, worker_uuid, build_uuid)
      _state = _state.
        remove_pending(job.name).
        remove_running(job.name).
        make_result(result_name,
          result.process_result,
          result.output_shasum,
          job.start_date,
          node_info = job.node_info)
    }

    for (name <- next_jobs(_state)) {
      if (is_session_name(name)) {
        if (build_context.sessions_structure.defined(name)) {
          _state.ancestor_results(name) match {
            case Some(results) => _state = start_session(_state, name, results)
            case None => warning("Bad build job " + quote(name) + ": no ancestor results")
          }
        }
        else warning("Bad build job " + quote(name) + ": no session info")
      }
      else warning("Bad build job " + quote(name))
    }
  }

  def run(): Build.Results = {
    val vacuous =
      synchronized_database("Build_Process.init") {
        _build_cluster.init()
        init_unsynchronized()
        build_context.master && _state.pending.isEmpty
      }
    if (vacuous) {
      progress.echo_warning("Nothing to build")
      if (build_context.master) stop_build()
      Build.Results(build_context)
    }
    else {
      start_worker()
      _build_cluster.start()

      try {
        while (!finished()) {
          synchronized_database("Build_Process.main") {
            if (progress.stopped) _state.build_running.foreach(_.cancel())
            main_unsynchronized()
            if (build_context.master && _state.exists_ready) {
              build_send(Build_Process.private_data.channel_ready)
            }
          }
          while(!build_action()) {}
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
