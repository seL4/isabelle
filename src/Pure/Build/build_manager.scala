/*  Title:      Pure/Build/build_manager.scala
    Author:     Fabian Huch, TU Muenchen

Isabelle manager for automated and quasi-interactive builds, with web frontend.
*/

package isabelle


import scala.collection.mutable
import scala.annotation.tailrec


object Build_Manager {
  /* task state synchronized via db */

  object Component {
    def parse(s: String): Component =
      space_explode('/', s) match {
        case name :: rev :: Nil => Component(name, rev)
        case _ => error("Malformed component: " + quote(s))
      }

    def AFP(rev: String = "") = Component("AFP", rev)
  }

  case class Component(name: String, rev: String = "") {
    override def toString: String = name + "/" + rev
  }

  sealed trait Build_Config {
    def name: String
    def components: List[Component]
    def fresh_build: Boolean
    def command(build_hosts: List[Build_Cluster.Host]): String
  }

  case class CI_Build(name: String, components: List[Component]) extends Build_Config {
    def fresh_build: Boolean = true
    def command(build_hosts: List[Build_Cluster.Host]): String = " ci_build " + name
  }

  object User_Build {
    val name: String = "user"
  }

  case class User_Build(
    afp_rev: Option[String] = None,
    prefs: List[Options.Spec] = Nil,
    requirements: Boolean = false,
    all_sessions: Boolean = false,
    base_sessions: List[String] = Nil,
    exclude_session_groups: List[String] = Nil,
    exclude_sessions: List[String] = Nil,
    session_groups: List[String] = Nil,
    sessions: List[String] = Nil,
    build_heap: Boolean = false,
    clean_build: Boolean = false,
    export_files: Boolean = false,
    fresh_build: Boolean = false,
    presentation: Boolean = false
  ) extends Build_Config {
    def name: String = User_Build.name
    def components: List[Component] = afp_rev.map(Component.AFP).toList
    def command(build_hosts: List[Build_Cluster.Host]): String = {
      " build" +
        if_proper(afp_rev, " -A:") +
        base_sessions.map(session => " -B " + Bash.string(session)).mkString +
        if_proper(build_hosts, build_hosts.map(host => " -H " + Bash.string(host.print)).mkString) +
        if_proper(presentation, " -P:") +
        if_proper(requirements, " -R") +
        if_proper(all_sessions, " -a") +
        if_proper(build_heap, " -b") +
        if_proper(clean_build, " -c") +
        if_proper(export_files, " -e") +
        if_proper(fresh_build, " -f") +
        Options.Spec.bash_strings(prefs, bg = true) +
        " -v" +
        sessions.map(session => " " + Bash.string(session)).mkString
    }
  }

  enum Priority { case low, normal, high }

  sealed trait T extends Library.Named

  sealed case class Task(
    build_config: Build_Config,
    id: UUID.T = UUID.random(),
    submit_date: Date = Date.now(),
    priority: Priority = Priority.normal,
    isabelle_rev: String = ""
  ) extends T {
    def name: String = id.toString
    def kind: String = build_config.name
    def components: List[Component] = build_config.components
  }

  sealed case class Job(
    id: UUID.T,
    kind: String,
    number: Long,
    isabelle_rev: String,
    components: List[Component],
    start_date: Date = Date.now(),
    cancelled: Boolean = false
  ) extends T { def name: String = kind + "/" + number }

  object Status {
    def from_result(result: Process_Result): Status = {
      if (result.ok) Status.ok
      else if (result.interrupted) Status.cancelled
      else Status.failed
    }
  }

  enum Status { case ok, cancelled, aborted, failed  }

  sealed case class Result(
    kind: String,
    number: Long,
    status: Status,
    id: Option[UUID.T] = None,
    date: Date = Date.now(),
    serial: Long = 0,
  ) extends T { def name: String = kind + "/" + number }

  object State {
    def max_serial(serials: Iterable[Long]): Long = serials.maxOption.getOrElse(0L)
    def inc_serial(serial: Long): Long = {
      require(serial < Long.MaxValue, "number overflow")
      serial + 1
    }

    type Pending = Library.Update.Data[Task]
    type Running = Library.Update.Data[Job]
    type Finished = Map[String, Result]
  }

  sealed case class State(
    serial: Long = 0,
    pending: State.Pending = Map.empty,
    running: State.Running = Map.empty,
    finished: State.Finished = Map.empty
  ) {
    def next_serial: Long = State.inc_serial(serial)

    def add_pending(task: Task): State = copy(pending = pending + (task.name -> task))
    def remove_pending(name: String): State = copy(pending = pending - name)

    def num_builds = running.size + finished.size

    def next: List[Task] =
      if (pending.isEmpty) Nil
      else {
        val priority = pending.values.map(_.priority).maxBy(_.ordinal)
        pending.values.filter(_.priority == priority).toList.sortBy(_.submit_date)(Date.Ordering)
      }

    def add_running(job: Job): State = copy(running = running + (job.name -> job))
    def remove_running(name: String): State = copy(running = running - name)

    def add_finished(result: Result): State = copy(finished = finished + (result.name -> result))

    lazy val kinds = (
      pending.values.map(_.kind) ++
      running.values.map(_.kind) ++
      finished.values.map(_.kind)).toList.distinct

    def next_number(kind: String): Long = {
      val serials = get_finished(kind).map(_.number) ::: get_running(kind).map(_.number)
      State.inc_serial(State.max_serial(serials))
    }

    def get_running(kind: String): List[Job] =
      (for ((_, job) <- running if job.kind == kind) yield job).toList

    def get_finished(kind: String): List[Result] =
      (for ((_, result) <- finished if result.kind == kind) yield result).toList

    def get(name: String): Option[T] =
      pending.get(name).orElse(running.get(name)).orElse(finished.get(name))

    def get(id: UUID.T): Option[T] =
      pending.values.find(_.id == id).orElse(
        running.values.find(_.id == id)).orElse(
        finished.values.find(_.id.contains(id)))
  }


  /* SQL data model */

  object private_data extends SQL.Data("isabelle_build_manager") {
    /* tables */

    override lazy val tables: SQL.Tables =
      SQL.Tables(State.table, Pending.table, Running.table, Finished.table)


    /* state */

    object State {
      val serial = SQL.Column.long("serial").make_primary_key

      val table = make_table(List(serial), name = "state")
    }

    def read_serial(db: SQL.Database): Long =
      db.execute_query_statementO[Long](
        State.table.select(List(State.serial.max)),
        _.long(State.serial)).getOrElse(0L)

    def pull_state(db: SQL.Database, state: State): State = {
      val serial_db = read_serial(db)
      if (serial_db == state.serial) state
      else {
        val serial = serial_db max state.serial

        val pending = pull_pending(db)
        val running = pull_running(db)
        val finished = pull_finished(db, state.finished)

        state.copy(serial = serial, pending = pending, running = running, finished = finished)
      }
    }

    def push_state(db: SQL.Database, old_state: State, state: State): State = {
      val finished = push_finished(db, state.finished)
      val updates =
        List(
          update_pending(db, old_state.pending, state.pending),
          update_running(db, old_state.running, state.running),
        ).filter(_.defined)

      if (updates.isEmpty && finished == old_state.finished) state
      else {
        val serial = state.next_serial
        db.execute_statement(State.table.delete(State.serial.where_equal(old_state.serial)))
        db.execute_statement(State.table.insert(), body =
          { (stmt: SQL.Statement) =>
            stmt.long(1) = serial
          })
        state.copy(serial = serial, finished = finished)
      }
    }


    /* pending */

    object Pending {
      val kind = SQL.Column.string("kind")
      val id = SQL.Column.string("id").make_primary_key
      val submit_date = SQL.Column.date("submit_date")
      val priority = SQL.Column.string("priority")
      val isabelle_rev = SQL.Column.string("isabelle_rev")
      val components = SQL.Column.string("components")

      val prefs = SQL.Column.string("prefs")
      val requirements = SQL.Column.bool("requirements")
      val all_sessions = SQL.Column.bool("all_sessions")
      val base_sessions = SQL.Column.string("base_sessions")
      val exclude_session_groups = SQL.Column.string("exclude_session_groups")
      val exclude_sessions = SQL.Column.string("exclude_sessions")
      val session_groups = SQL.Column.string("session_groups")
      val sessions = SQL.Column.string("sessions")
      val build_heap = SQL.Column.bool("build_heap")
      val clean_build = SQL.Column.bool("clean_build")
      val export_files = SQL.Column.bool("export_files")
      val fresh_build = SQL.Column.bool("fresh_build")
      val presentation = SQL.Column.bool("presentation")

      val table =
        make_table(List(kind, id, submit_date, priority, isabelle_rev, components, prefs,
          requirements, all_sessions, base_sessions, exclude_session_groups, exclude_sessions,
          session_groups, sessions, build_heap, clean_build, export_files, fresh_build,
          presentation),
        name = "pending")
    }

    def pull_pending(db: SQL.Database): Build_Manager.State.Pending =
      db.execute_query_statement(Pending.table.select(), Map.from[String, Task], get =
        { res =>
          val kind = res.string(Pending.kind)
          val id = res.string(Pending.id)
          val submit_date = res.date(Pending.submit_date)
          val priority = Priority.valueOf(res.string(Pending.priority))
          val isabelle_rev = res.string(Pending.isabelle_rev)
          val components = space_explode(',', res.string(Pending.components)).map(Component.parse)

          val build_config =
            if (kind != User_Build.name) CI_Build(kind, components)
            else {
              val prefs = Options.Spec.parse(res.string(Pending.prefs))
              val requirements = res.bool(Pending.requirements)
              val all_sessions = res.bool(Pending.all_sessions)
              val base_sessions = space_explode(',', res.string(Pending.base_sessions))
              val exclude_session_groups =
                space_explode(',', res.string(Pending.exclude_session_groups))
              val exclude_sessions = space_explode(',', res.string(Pending.exclude_sessions))
              val session_groups = space_explode(',', res.string(Pending.session_groups))
              val sessions = space_explode(',', res.string(Pending.sessions))
              val build_heap = res.bool(Pending.build_heap)
              val clean_build = res.bool(Pending.clean_build)
              val export_files = res.bool(Pending.export_files)
              val fresh_build = res.bool(Pending.fresh_build)
              val presentation = res.bool(Pending.presentation)

              val afp_rev = components.find(_.name == Component.AFP().name).map(_.rev)
              User_Build(afp_rev, prefs, requirements, all_sessions, base_sessions,
                exclude_session_groups, exclude_sessions, session_groups, sessions, build_heap,
                clean_build, export_files, fresh_build, presentation)
            }

          val task = Task(build_config, UUID.make(id), submit_date, priority, isabelle_rev)

          task.name -> task
        })

    def update_pending(
      db: SQL.Database,
      old_pending: Build_Manager.State.Pending,
      pending: Build_Manager.State.Pending
    ): Library.Update = {
      val update = Library.Update.make(old_pending, pending)
      val delete = update.delete.map(old_pending(_).id.toString)

      if (update.deletes)
        db.execute_statement(Pending.table.delete(Pending.id.where_member(delete)))

      if (update.inserts) {
        db.execute_batch_statement(Pending.table.insert(), batch =
          for (name <- update.insert) yield { (stmt: SQL.Statement) =>
            val task = pending(name)
            stmt.string(1) = task.kind
            stmt.string(2) = task.id.toString
            stmt.date(3) = task.submit_date
            stmt.string(4) = task.priority.toString
            stmt.string(5) = task.isabelle_rev
            stmt.string(6) = task.components.mkString(",")

            def get[A](f: User_Build => A): Option[A] =
              task.build_config match {
                case user_build: User_Build => Some(f(user_build))
                case _ => None
              }

            stmt.string(7) = get(user_build => Options.Spec.bash_strings(user_build.prefs))
            stmt.bool(8) = get(_.requirements)
            stmt.bool(9) = get(_.all_sessions)
            stmt.string(10) = get(_.base_sessions.mkString(","))
            stmt.string(11) = get(_.exclude_session_groups.mkString(","))
            stmt.string(12) = get(_.exclude_sessions.mkString(","))
            stmt.string(13) = get(_.session_groups.mkString(","))
            stmt.string(14) = get(_.sessions.mkString(","))
            stmt.bool(15) = get(_.build_heap)
            stmt.bool(16) = get(_.clean_build)
            stmt.bool(17) = get(_.export_files)
            stmt.bool(18) = get(_.fresh_build)
            stmt.bool(19) = get(_.presentation)
          })
      }

      update
    }


    /* running */

    object Running {
      val id = SQL.Column.string("id").make_primary_key
      val kind = SQL.Column.string("kind")
      val number = SQL.Column.long("number")
      val isabelle_rev = SQL.Column.string("isabelle_rev")
      val components = SQL.Column.string("components")
      val start_date = SQL.Column.date("start_date")
      val cancelled = SQL.Column.bool("cancelled")

      val table =
        make_table(List(id, kind, number, isabelle_rev, components, start_date, cancelled),
        name = "running")
    }

    def pull_running(db: SQL.Database): Build_Manager.State.Running =
      db.execute_query_statement(Running.table.select(), Map.from[String, Job], get =
        { res =>
          val id = res.string(Running.id)
          val kind = res.string(Running.kind)
          val number = res.long(Running.number)
          val isabelle_rev = res.string(Running.isabelle_rev)
          val components = space_explode(',', res.string(Running.components)).map(Component.parse)
          val start_date = res.date(Running.start_date)
          val cancelled = res.bool(Running.cancelled)

          val job =
            Job(UUID.make(id), kind, number, isabelle_rev, components, start_date, cancelled)

          job.name -> job
        })

    def update_running(
      db: SQL.Database,
      old_running: Build_Manager.State.Running,
      running: Build_Manager.State.Running
    ): Library.Update = {
      val update = Library.Update.make(old_running, running)
      val delete = update.delete.map(old_running(_).id.toString)

      if (update.deletes)
        db.execute_statement(Running.table.delete(Running.id.where_member(delete)))

      if (update.inserts) {
        db.execute_batch_statement(Running.table.insert(), batch =
          for (name <- update.insert) yield { (stmt: SQL.Statement) =>
            val job = running(name)
            stmt.string(1) = job.id.toString
            stmt.string(2) = job.kind
            stmt.long(3) = job.number
            stmt.string(4) = job.isabelle_rev
            stmt.string(5) = job.components.mkString(",")
            stmt.date(6) = job.start_date
            stmt.bool(7) = job.cancelled
          })
      }
      update
    }


    /* finished */

    object Finished {
      val kind = SQL.Column.string("kind")
      val number = SQL.Column.long("number")
      val status = SQL.Column.string("status")
      val id = SQL.Column.string("id")
      val date = SQL.Column.date("date")
      val serial = SQL.Column.long("serial").make_primary_key

      val table = make_table(List(kind, number, status, id, date, serial), name = "finished")
    }

    def read_finished_serial(db: SQL.Database): Long =
      db.execute_query_statementO[Long](
        Finished.table.select(List(Finished.serial.max)),
        _.long(Finished.serial)).getOrElse(0L)

    def pull_finished(
      db: SQL.Database,
      finished: Build_Manager.State.Finished
    ): Build_Manager.State.Finished = {
      val max_serial0 = Build_Manager.State.max_serial(finished.values.map(_.serial))
      val max_serial1 = read_finished_serial(db)
      val missing = (max_serial0 + 1) to max_serial1
      finished ++ db.execute_query_statement(
        Finished.table.select(sql = Finished.serial.where_member_long(missing)),
        Map.from[String, Result], get =
        { res =>
          val kind = res.string(Finished.kind)
          val number = res.long(Finished.number)
          val status = Status.valueOf(res.string(Finished.status))
          val id = res.get_string(Finished.id).map(UUID.make)
          val date = res.date(Finished.date)
          val serial = res.long(Finished.serial)

          val result = Result(kind, number, status, id, date, serial)
          result.name -> result
        }
      )
    }

    def push_finished(
      db: SQL.Database,
      finished: Build_Manager.State.Finished
    ): Build_Manager.State.Finished = {
      val (insert0, old) = finished.partition(_._2.serial == 0L)
      val max_serial = Build_Manager.State.max_serial(finished.map(_._2.serial))
      val insert =
        for (((_, result), n) <- insert0.zipWithIndex)
        yield result.copy(serial = max_serial + 1 + n)

      if (insert.nonEmpty)
        db.execute_batch_statement(Finished.table.insert(), batch =
          for (result <- insert) yield { (stmt: SQL.Statement) =>
            stmt.string(1) = result.kind
            stmt.long(2) = result.number
            stmt.string(3) = result.status.toString
            stmt.string(4) = result.id.map(_.toString)
            stmt.date(5) = result.date
            stmt.long(6) = result.serial
          })

      old ++ insert.map(result => result.serial.toString -> result)
    }
  }


  /* running build manager processes */

  abstract class Loop_Process[A](name: String, store: Store, progress: Progress)
    extends Runnable {
    val options = store.options

    private val _database =
      try { store.open_database() }
      catch { case exn: Throwable => close(); throw exn }

    def close(): Unit = Option(_database).foreach(_.close())

    protected var _state = State()

    protected def synchronized_database[A](label: String)(body: => A): A = synchronized {
      Build_Manager.private_data.transaction_lock(_database, label = name + "." + label) {
        val old_state = Build_Manager.private_data.pull_state(_database, _state)
        _state = old_state
        val res = body
        _state = Build_Manager.private_data.push_state(_database, old_state, _state)
        res
      }
    }

    protected def delay = options.seconds("build_manager_delay")

    def init: A
    def loop_body(a: A): A
    def stopped(a: A): Boolean = progress.stopped

    private val interrupted = Synchronized(false)
    private def sleep(time_limit: Time): Unit =
      interrupted.timed_access(_ => Some(time_limit), b => if (b) Some((), false) else None)
    def interrupt(): Unit = interrupted.change(_ => true)

    @tailrec private def loop(a: A): Unit =
      if (!stopped(a)) {
        val start = Time.now()
        val a1 = loop_body(a)
        if (!stopped(a)) {
          sleep(start + delay)
          loop(a1)
        }
      }

    override def run(): Unit = {
      progress.echo("Started " + name)
      loop(init)
      close()
      progress.echo("Stopped " + name)
    }

    def echo(msg: String) = progress.echo(name + ": " + msg)
    def echo_error_message(msg: String) = progress.echo_error_message(name + ": " + msg)
  }


  /* build runner */

  object Runner {
    object State {
      def empty: State = new State(Map.empty, Map.empty)
    }

    class State private(
      processes: Map[String, Future[Bash.Process]],
      results: Map[String, Future[Process_Result]]
    ) {
      def is_empty = processes.isEmpty && results.isEmpty

      def init(build_config: Build_Config, job: Job, context: Context): State = {
        val process = Future.fork(context.process(build_config))
        val result =
          Future.fork(
            process.join_result match {
              case Exn.Res(res) => context.run(res)
              case Exn.Exn(_) => Process_Result(Process_Result.RC.interrupt)
            })
        new State(processes + (job.name -> process), results + (job.name -> result))
      }

      def running: List[String] = processes.keys.toList

      def update: (State, Map[String, Process_Result]) = {
        val finished =
          for ((name, future) <- results if future.is_finished) yield name -> future.join

        val processes1 = processes.filterNot((name, _) => finished.contains(name))
        val results1 = results.filterNot((name, _) => finished.contains(name))

        (new State(processes1, results1), finished)
      }

      def cancel(cancelled: List[String]): State = {
        for (name <- cancelled) {
          val process = processes(name)
          if (process.is_finished) process.join.interrupt()
          else process.cancel()
        }

        new State(processes.filterNot((name, _) => cancelled.contains(name)), results)
      }
    }
  }

  class Runner(
    store: Store,
    build_hosts: List[Build_Cluster.Host],
    isabelle_repository: Mercurial.Repository,
    sync_dirs: List[Sync.Dir],
    progress: Progress
  ) extends Loop_Process[Runner.State]("Runner", store, progress) {
    val rsync_context = Rsync.Context()

    private def sync(repository: Mercurial.Repository, rev: String, target: Path): String = {
      repository.pull()

      if (rev.nonEmpty) repository.sync(rsync_context, target, rev = rev)

      Exn.capture(repository.id(File.read(target + Mercurial.Hg_Sync.PATH_ID))) match {
        case Exn.Res(res) => res
        case Exn.Exn(exn) => ""
      }
    }

    private def start_next(): Option[(Build_Config, Job)] =
      synchronized_database("start_job") {
        _state.next.headOption.flatMap { task =>
          progress.echo("Initializing " + task.name)

          _state = _state.remove_pending(task.name)

          val context = Context(store, task, build_hosts)
          val number = _state.next_number(task.kind)

          Exn.capture {
            val isabelle_rev =
              sync(isabelle_repository, task.isabelle_rev, context.isabelle_dir)

            val components =
              for (component <- task.components)
              yield sync_dirs.find(_.name == component.name) match {
                case Some(sync_dir) =>
                  val target = context.isabelle_dir + sync_dir.target
                  component.copy(rev = sync(sync_dir.hg, component.rev, target))
                case None =>
                  if (component.rev.isEmpty) component
                  else error("Unknown component " + component)
              }

            Job(task.id, task.kind, number, isabelle_rev, components)
          } match {
            case Exn.Res(job) =>
              _state = _state.add_running(job)
              val context1 = context.move(Context(store, job))

              val msg = "Starting " + job.name
              echo(msg + " (id " + job.id + ")")
              context1.progress.echo(msg)

              Some(task.build_config, job)
            case Exn.Exn(exn) =>
              val result = Result(task.kind, number, Status.aborted)
              val context1 = Context(store, result)

              val msg = "Failed to start job: " + exn.getMessage
              echo_error_message(msg)
              context1.progress.echo_error_message(msg)

              context.remove()
              _state = _state.add_finished(result)

              None
          }
        }
      }

    private def stop_cancelled(state: Runner.State): Runner.State =
      synchronized_database("stop_cancelled") {
        val cancelled = for (name <- state.running if _state.running(name).cancelled) yield name
        state.cancel(cancelled)
      }

    private def finish_job(name: String, process_result: Process_Result): Unit =
      synchronized_database("finish_job") {
        val job = _state.running(name)
        val context = Context(store, job, build_hosts)

        val result = Result(job.kind, job.number, Status.from_result(process_result), Some(job.id))
        context.copy_results(Context(store, result))
        context.remove()
        echo("Finished job " + job.id + " with status code " + process_result.rc)

        _state = _state
          .remove_running(job.name)
          .add_finished(result)
      }

    override def stopped(state: Runner.State): Boolean = progress.stopped && state.is_empty

    def init: Runner.State = Runner.State.empty
    def loop_body(state: Runner.State): Runner.State = {
      if (state.is_empty && !progress.stopped) {
        start_next() match {
          case None => state
          case Some((build_config, job)) =>
            state.init(build_config, job, Context(store, job, build_hosts))
        }
      }
      else {
        val (state1, results) = stop_cancelled(state).update
        results.foreach(finish_job)
        state1
      }
    }
  }


  /* repository poller */

  object Poller {
    case class State(ids: List[String], next: Future[List[String]])
  }

  class Poller(
    ci_jobs: List[String],
    store: Store,
    isabelle_repository: Mercurial.Repository,
    sync_dirs: List[Sync.Dir],
    progress: Progress
  ) extends Loop_Process[Poller.State]("Poller", store, progress) {

    override def delay = options.seconds("build_manager_poll_delay")

    private def ids: List[String] =
      isabelle_repository.id("default") :: sync_dirs.map(_.hg.id("default"))

    private def poll: Future[List[String]] = Future.fork {
      Par_List.map((repo: Mercurial.Repository) => repo.pull(),
        isabelle_repository :: sync_dirs.map(_.hg))

      ids
    }

    val init: Poller.State = Poller.State(ids, poll)

    def ci_task(name: String): Task =
      Task(CI_Build(name, sync_dirs.map(dir => Component(dir.name, "default"))),
        priority = Priority.low, isabelle_rev = "default")

    private def add_task(): Unit = synchronized_database("add_task") {
      for (name <- ci_jobs if !_state.pending.values.exists(_.kind == name)) {
        _state = _state.add_pending(ci_task(name))
      }
    }

    def loop_body(state: Poller.State): Poller.State =
      if (!state.next.is_finished) state
      else {
        state.next.join_result match {
          case Exn.Exn(exn) =>
            echo_error_message("Could not reach repository: " + exn.getMessage)
            Poller.State(state.ids, poll)
          case Exn.Res(ids1) =>
            if (state.ids != ids1) {
              echo("Found new revisions: " + ids1)
              add_task()
            }
            Poller.State(ids1, poll)
        }
      }
  }


  /* web server */

  object Web_Server {
    object Page {
      val HOME = Path.basic("home")
      val OVERVIEW = Path.basic("overview")
      val BUILD = Path.basic("build")
    }

    object API {
      val BUILD_CANCEL = Path.explode("api/build/cancel")
      val CSS = Path.explode("api/isabelle.css")
    }

    object Cache {
      def empty: Cache = new Cache()
    }

    class Cache private(keep: Time = Time.minutes(1)) {
      var logs: Map[String, (Time, String)] = Map.empty

      def update(store: Store, state: State): Unit = synchronized {
        logs =
          for {
            (name, (time, log)) <- logs
            if time + keep > Time.now()
          } yield name -> (time, Context(store, state.get(name).get).log)
      }

      def lookup(store: Store, elem: T): String = synchronized {
        logs.get(elem.name) match {
          case Some((_, log)) =>
            logs += elem.name -> (Time.now(), log)
          case None =>
            logs += elem.name -> (Time.now(), Context(store, elem).log)
        }
        logs(elem.name)._2
      }
    }
  }

  class Web_Server(port: Int, paths: Web_App.Paths, store: Store, progress: Progress)
    extends Loop_Process[Unit]("Web_Server", store, progress) {
    import Web_App.*
    import Web_Server.*

    val cache = Cache.empty
    val Id = new Properties.String(Markup.ID)

    enum Model {
      case Error extends Model
      case Cancelled extends Model
      case Home(state: State) extends Model
      case Overview(kind: String, state: State) extends Model
      case Build(elem: T, state: State, public: Boolean = true) extends Model
    }

    object View {
      import HTML.*
      import More_HTML.*

      def render_if(cond: Boolean, body: XML.Body): XML.Body = if (cond) body else Nil

      def frontend_link(url: Url, xml: XML.Body): XML.Elem =
        link(url.toString, xml) + ("target" -> "_parent")

      def link_kind(kind: String): XML.Elem =
        frontend_link(paths.frontend_url(Page.OVERVIEW, Markup.Kind(kind)), text(kind))
      def link_build(name: String, number: Long): XML.Elem =
        frontend_link(paths.frontend_url(Page.BUILD, Markup.Name(name)), text("#" + number))

      def render_home(state: State): XML.Body = {
        def render_kind(kind: String): XML.Elem = {
          val running = state.get_running(kind).sortBy(_.number).reverse
          val finished = state.get_finished(kind).sortBy(_.number).reverse

          def render_previous(finished: List[Result]): XML.Body = {
            val (failed, rest) = finished.span(_.status != Status.ok)
            val first_failed = failed.lastOption.map(result =>
              par(
                text("first failure: ") :::
                link_build(result.name, result.number) ::
                text(" on " + result.date)))
            val last_success = rest.headOption.map(result =>
              par(
                text("last success: ") ::: link_build(result.name, result.number) ::
                text(" on " + result.date)))
            first_failed.toList ::: last_success.toList
          }

          def render_job(job: Job): XML.Body =
            par(link_build(job.name, job.number) :: text(": running since " + job.start_date)) ::
            render_if(finished.headOption.exists(_.status != Status.ok), render_previous(finished))

          def render_result(result: Result): XML.Body =
            par(
              link_build(result.name, result.number) ::
              text(" (" + result.status.toString + ") on " + result.date)) ::
            render_if(result.status != Status.ok, render_previous(finished.tail))

          fieldset(
            XML.elem("legend", List(link_kind(kind))) ::
            (if (running.nonEmpty) render_job(running.head)
            else if (finished.nonEmpty) render_result(finished.head)
            else Nil))
        }

        chapter("Dashboard") ::
          text("Queue: " + state.pending.size + " tasks waiting") :::
          section("Builds") :: text("Total: " + state.num_builds + " builds") :::
          state.kinds.map(render_kind)
      }

      def render_overview(kind: String, state: State): XML.Body = {
        def render_job(job: Job): XML.Body =
          List(par(link_build(job.name, job.number) :: text(" running since " + job.start_date)))

        def render_result(result: Result): XML.Body =
          List(par(
            link_build(result.name, result.number) ::
            text(" (" + result.status + ") on " + result.date)))

        chapter(kind) ::
          itemize(
            state.get_running(kind).sortBy(_.number).reverse.map(render_job) :::
            state.get_finished(kind).sortBy(_.number).reverse.map(render_result)) :: Nil
      }

      private val ID = Params.key(Markup.ID)

      def render_build(elem: T, state: State, public: Boolean): XML.Body = {
        def render_cancel(id: UUID.T): XML.Body =
          render_if(!public, List(
            submit_form("", List(hidden(ID, id.toString),
              api_button(paths.api_route(API.BUILD_CANCEL), "cancel build")))))

        def render_rev(isabelle_rev: String, components: List[Component]): XML.Body =
          for {
            component <- Component("Isabelle", isabelle_rev) :: components
            if component.rev.nonEmpty
          } yield par(text(component.toString))

        chapter("Build " + elem.name) :: (elem match {
          case task: Task =>
            par(text("Task from " + task.submit_date + ". ")) ::
            render_rev(task.isabelle_rev, task.components) :::
            render_cancel(task.id)
          case job: Job =>
            par(text("Start: " + job.start_date)) ::
            par(
              if (job.cancelled) text("Cancelling...")
              else text("Running...") ::: render_cancel(job.id)) ::
            render_rev(job.isabelle_rev, job.components) :::
            source(cache.lookup(store, job)) :: Nil
          case result: Result =>
            par(text("Date: " + result.date)) ::
            par(text("Status: " + result.status)) ::
            source(cache.lookup(store, result)) :: Nil
        })
      }

      def render_cancelled: XML.Body =
        List(chapter("Build Cancelled"), frontend_link(paths.frontend_url(Page.HOME), text("Home")))

      def parse_id(params: Params.Data): Option[UUID.T] =
        for {
          id <- params.get(ID)
          uuid <- UUID.unapply(id)
        } yield uuid
    }

    private val server = new Server[Model](paths, port, progress = progress) {
      /* control */

      def overview: Some[Model.Home] = Some(Model.Home(_state))

      def get_overview(props: Properties.T): Option[Model.Overview] =
        props match {
          case Markup.Kind(kind) => Some(Model.Overview(kind, _state))
          case _ => None
        }

      def get_build(props: Properties.T): Option[Model.Build] =
        props match {
          case Markup.Name(name) =>
            val state = _state
            state.get(name).map(Model.Build(_, state))
          case Id(UUID(id)) =>
            val state = _state
            state.get(id).map(Model.Build(_, state, public = false))
          case _ => None
        }

      def cancel_build(params: Params.Data): Option[Model] =
        for {
          id <- View.parse_id(params)
          model <-
            synchronized_database("cancel_build") {
              _state.get(id).map {
                case task: Task =>
                  _state = _state.remove_pending(task.name)
                  Model.Cancelled
                case job: Job =>
                  val job1 = job.copy(cancelled = true)
                  _state = _state
                    .remove_running(job.name)
                    .add_running(job1)
                  Model.Build(job1, _state, public = false)
                case result: Result => Model.Build(result, _state, public = false)
              }
            }
        } yield model

      def render(model: Model): XML.Body =
        HTML.title("Isabelle Build Manager") :: (
          model match {
            case Model.Error => HTML.text("invalid request")
            case Model.Home(state) => View.render_home(state)
            case Model.Overview(kind, state) => View.render_overview(kind, state)
            case Model.Build(elem, state, public) => View.render_build(elem, state, public)
            case Model.Cancelled => View.render_cancelled
          })

      val error_model: Model = Model.Error
      val endpoints = List(
        Get(Page.HOME, "home", _ => overview),
        Get(Page.OVERVIEW, "overview", get_overview),
        Get(Page.BUILD, "build", get_build),
        Post(API.BUILD_CANCEL, "cancel build", cancel_build),
        Get_File(API.CSS, "css", _ => Some(HTML.isabelle_css)))
      val head = List(HTML.style_file(paths.api_route(API.CSS)))
    }

    def init: Unit = server.start()
    def loop_body(u: Unit): Unit = {
      if (progress.stopped) server.stop()
      else synchronized_database("iterate") { cache.update(store, _state) }
    }
  }


  /* context */

  object Context {
    def apply(store: Store, elem: T, build_hosts: List[Build_Cluster.Host] = Nil): Context =
      new Context(store, store.dir(elem), build_hosts)
  }

  class Context private(store: Store, val dir: Path, val build_hosts: List[Build_Cluster.Host]) {
    def isabelle_dir: Path = dir + Path.basic("isabelle")

    private val log_file = dir + Path.basic("log")
    val progress = new File_Progress(log_file, verbose = true)
    def log: String =
      Exn.capture(File.read(log_file)) match {
        case Exn.Exn(_) => ""
        case Exn.Res(res) => res
      }

    def move(other: Context): Context = {
      Isabelle_System.make_directory(other.dir.dir)
      Isabelle_System.move_file(dir, other.dir)
      other
    }

    def copy_results(other: Context): Context = {
      Isabelle_System.make_directory(other.dir)
      Isabelle_System.copy_file(log_file, other.log_file)
      other
    }

    def remove(): Unit = Isabelle_System.rm_tree(dir)

    lazy val ssh = store.open_ssh()

    def process(build_config: Build_Config): Bash.Process = {
      val isabelle = Other_Isabelle(isabelle_dir, store.identifier, ssh, progress)

      val init_components =
        for {
          dir <- build_config.components
          target = isabelle_dir + Sync.DIRS + Path.basic(dir.name)
          if Components.is_component_dir(target)
        } yield "init_component " + quote(target.absolute.implode)

      isabelle.init(other_settings = isabelle.init_components() ::: init_components,
        fresh = build_config.fresh_build, echo = true)

      val cmd = build_config.command(build_hosts)
      progress.echo("isabelle" + cmd)

      val script = File.bash_path(Isabelle_Tool.exe(isabelle.isabelle_home)) + cmd
      ssh.bash_process(isabelle.bash_context(script), settings = false)
    }

    def run(process: Bash.Process): Process_Result = {
      val process_result =
        process.result(progress_stdout = progress.echo(_), progress_stderr = progress.echo(_))
      ssh.close()
      process_result
    }
  }


  /* build manager store */

  case class Store(options: Options) {
    val base_dir = Path.explode(options.string("build_manager_dir"))
    val identifier = options.string("build_manager_identifier")

    def dir(elem: T): Path = base_dir + (
      elem match {
        case task: Task => Path.make(List("pending", task.id.toString))
        case job: Job => Path.make(List("running", job.kind, job.number.toString))
        case result: Result => Path.make(List("finished", result.kind, result.number.toString))
      })

    def open_ssh(): SSH.Session =
      SSH.open_session(options,
        host = options.string("build_manager_ssh_host"),
        port = options.int("build_manager_ssh_port"),
        user = options.string("build_manager_ssh_user"))

    def open_database(server: SSH.Server = SSH.no_server): PostgreSQL.Database =
      PostgreSQL.open_database_server(options, server = server,
        user = options.string("build_manager_database_user"),
        password = options.string("build_manager_database_password"),
        database = options.string("build_manager_database_name"),
        host = options.string("build_manager_database_host"),
        port = options.int("build_manager_database_port"),
        ssh_host = options.string("build_manager_database_ssh_host"),
        ssh_port = options.int("build_manager_database_ssh_port"),
        ssh_user = options.string("build_manager_database_ssh_user"))

    def open_postgresql_server(): SSH.Server =
      PostgreSQL.open_server(options,
        host = options.string("build_manager_database_host"),
        port = options.int("build_manager_database_port"),
        ssh_host = options.string("build_manager_ssh_host"),
        ssh_port = options.int("build_manager_ssh_port"),
        ssh_user = options.string("build_manager_ssh_user"))
  }


  /* build manager */

  def build_manager(
    build_hosts: List[Build_Cluster.Host],
    options: Options,
    port: Int,
    sync_dirs: List[Sync.Dir] = Nil,
    progress: Progress = new Progress
  ): Unit = {
    val store = Store(options)
    val isabelle_repository = Mercurial.self_repository()
    val ci_jobs = space_explode(',', options.string("build_manager_ci_jobs"))
    val url = Url(options.string("build_manager_address"))
    val paths = Web_App.Paths(url, Path.current, true, Web_Server.Page.HOME)

    using(store.open_database())(db =>
      Build_Manager.private_data.transaction_lock(db,
        create = true, label = "Build_Manager.build_manager") {})

    val processes = List(
      new Runner(store, build_hosts, isabelle_repository, sync_dirs, progress),
      new Poller(ci_jobs, store, isabelle_repository, sync_dirs, progress),
      new Web_Server(port, paths, store, progress))

    val threads = processes.map(Isabelle_Thread.create(_))
    POSIX_Interrupt.handler {
      progress.stop()
      processes.foreach(_.interrupt())
    } {
      threads.foreach(_.start())
      threads.foreach(_.join())
    }
  }

  def build_task(
    options: Options,
    store: Store,
    afp_root: Option[Path] = None,
    base_sessions: List[String] = Nil,
    presentation: Boolean = false,
    requirements: Boolean = false,
    exclude_session_groups: List[String] = Nil,
    all_sessions: Boolean = false,
    build_heap: Boolean = false,
    clean_build: Boolean = false,
    export_files: Boolean = false,
    fresh_build: Boolean = false,
    session_groups: List[String] = Nil,
    sessions: List[String] = Nil,
    prefs: List[Options.Spec] = Nil,
    exclude_sessions: List[String] = Nil,
    progress: Progress = new Progress
  ): UUID.T = {
    val id = UUID.random()
    val afp_rev = if (afp_root.nonEmpty) Some("") else None

    val build_config = User_Build(afp_rev, prefs, requirements, all_sessions, base_sessions,
      exclude_session_groups, exclude_sessions, session_groups, sessions, build_heap, clean_build,
      export_files, fresh_build, presentation)
    val task = Task(build_config, id, Date.now(), Priority.high)

    val context = Context(store, task)

    progress.interrupt_handler {
      using(store.open_ssh()) { ssh =>
        val rsync_context = Rsync.Context(ssh = ssh, chmod = "g+rwx")
        progress.echo("Transferring repositories...")
        Sync.sync(store.options, rsync_context, context.isabelle_dir, preserve_jars = true,
          dirs = Sync.afp_dirs(afp_root))
        ssh.execute("chmod g+rwx " + File.bash_path(context.dir))

        if (progress.stopped) {
          progress.echo("Cancelling submission...")
          ssh.rm_tree(context.dir)
        } else {
          using(store.open_postgresql_server()) { server =>
            using(store.open_database(server = server)) { db =>
              Build_Manager.private_data.transaction_lock(db, label = "Build_Manager.build_task") {
                val old_state = Build_Manager.private_data.pull_state(db, State())
                val state = old_state.add_pending(task)
                Build_Manager.private_data.push_state(db, old_state, state)
              }
            }
          }
          val address = options.string("build_manager_address") + "/build?id=" + task.id
          progress.echo("Submitted task. Private url: " + address)
        }
      }
    }

    id
  }


  /* Isabelle tool wrapper */

  private def show_options(relevant_options: List[String], options: Options): String =
    cat_lines(relevant_options.flatMap(options.get).map(_.print))

  private val notable_server_options =
    List(
      "build_manager_dir",
      "build_manager_address",
      "build_manager_ssh_host",
      "build_manager_ci_jobs")

  val isabelle_tool = Isabelle_Tool("build_manager", "run build manager", Scala_Project.here,
    { args =>
      var afp_root: Option[Path] = None
      val dirs = new mutable.ListBuffer[Path]
      val build_hosts = new mutable.ListBuffer[Build_Cluster.Host]
      var options = Options.init()
      var port = 8080

      val getopts = Getopts("""
Usage: isabelle build_manager [OPTIONS]

  Options are:
    -A ROOT      include AFP with given root directory (":" for """ + AFP.BASE.implode + """)
    -D DIR       include extra component in given directory
    -H HOSTS     additional cluster host specifications of the form
                 NAMES:PARAMETERS (separated by commas)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p PORT      explicit web server port

  Run Isabelle build manager. Notable system options:

""" + Library.indent_lines(2, show_options(notable_server_options, options)) + "\n",
        "A:" -> (arg => afp_root = Some(if (arg == ":") AFP.BASE else Path.explode(arg))),
        "D:" -> (arg => dirs += Path.explode(arg)),
        "H:" -> (arg => build_hosts ++= Build_Cluster.Host.parse(Registry.global, arg)),
        "o:" -> (arg => options = options + arg),
        "p:" -> (arg => port = Value.Int.parse(arg)))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()
      val sync_dirs =
        Sync.afp_dirs(afp_root) ::: dirs.toList.map(dir => Sync.Dir(dir.file_name, dir))

      sync_dirs.foreach(_.check())

      build_manager(build_hosts = build_hosts.toList, options = options, port = port,
        sync_dirs = sync_dirs, progress = progress)
    })

  val isabelle_tool1 = Isabelle_Tool("build_task", "submit build task for build manager",
    Scala_Project.here,
    { args =>
      var afp_root: Option[Path] = None
      val base_sessions = new mutable.ListBuffer[String]
      var presentation = false
      var requirements = false
      val exclude_session_groups = new mutable.ListBuffer[String]
      var all_sessions = false
      var build_heap = false
      var clean_build = false
      var export_files = false
      var fresh_build = false
      val session_groups = new mutable.ListBuffer[String]
      var options = Options.init(specs = Options.Spec.ISABELLE_BUILD_OPTIONS)
      var prefs: List[Options.Spec] = Nil
      val exclude_sessions = new mutable.ListBuffer[String]

      val getopts = Getopts("""
Usage: isabelle build_task [OPTIONS] [SESSIONS ...]

  Options are:
    -A ROOT      include AFP with given root directory (":" for """ + AFP.BASE.implode + """)
    -B NAME      include session NAME and all descendants
    -P           enable HTML/PDF presentation
    -R           refer to requirements of selected sessions
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -b           build heap images
    -c           clean build
    -e           export files from session specification into file-system
    -f           fresh build
    -g NAME      select session group NAME
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p OPTIONS   comma-separated preferences for build process
    -x NAME      exclude session NAME and all descendants

  Submit build task on SSH server. Notable system options:

""" + Library.indent_lines(2, show_options(List("build_manager_ssh_user"), options)) + "\n",
        "A:" -> (arg => afp_root = Some(if (arg == ":") AFP.BASE else Path.explode(arg))),
        "B:" -> (arg => base_sessions += arg),
        "P" -> (_ => presentation = true),
        "R" -> (_ => requirements = true),
        "X:" -> (arg => exclude_session_groups += arg),
        "a" -> (_ => all_sessions = true),
        "b" -> (_ => build_heap = true),
        "c" -> (_ => clean_build = true),
        "e" -> (_ => export_files = true),
        "f" -> (_ => fresh_build = true),
        "g:" -> (arg => session_groups += arg),
        "o:" -> (arg => options = options + arg),
        "p:" -> (arg => prefs = Options.Spec.parse(arg)),
        "x:" -> (arg => exclude_sessions += arg))

      val sessions = getopts(args)
      val store = Store(options)
      val progress = new Console_Progress()

      build_task(options, store = store, afp_root = afp_root, base_sessions =
        base_sessions.toList, presentation = presentation, requirements = requirements,
        exclude_session_groups = exclude_session_groups.toList, all_sessions = all_sessions,
        build_heap = build_heap, clean_build = clean_build, export_files = export_files,
        fresh_build = fresh_build, session_groups = session_groups.toList, sessions = sessions,
        prefs = prefs, exclude_sessions = exclude_sessions.toList, progress = progress)
    })
}

class Build_Manager_Tools extends Isabelle_Scala_Tools(
  Build_Manager.isabelle_tool, Build_Manager.isabelle_tool1)
