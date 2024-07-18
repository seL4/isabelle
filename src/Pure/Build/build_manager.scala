/*  Title:      Pure/Build/build_manager.scala
    Author:     Fabian Huch, TU Muenchen

Isabelle manager for automated and quasi-interactive builds, with web frontend.
*/

package isabelle


import scala.collection.mutable
import scala.annotation.tailrec


object Build_Manager {
  /** task state synchronized via db **/

  object Component {
    def parse(s: String): Component =
      space_explode('/', s) match {
        case name :: Nil => Component(name)
        case name :: rev :: Nil => Component(name, rev)
        case _ => error("Malformed component: " + quote(s))
      }

    val Isabelle = "Isabelle"
    val AFP = "AFP"

    def isabelle(rev: String = "") = Component(Isabelle, rev)
    def afp(rev: String = "") = Component(AFP, rev)
  }

  case class Component(name: String, rev: String = "") {
    override def toString: String = name + if_proper(rev, "/" + rev)

    def is_local: Boolean = rev.isEmpty
  }

  sealed trait Build_Config {
    def name: String
    def extra_components: List[Component]
    def fresh_build: Boolean
    def build_cluster: Boolean
    def command(job_url: Url, build_hosts: List[Build_Cluster.Host]): String
  }

  object CI_Build {
    def apply(job: Build_CI.Job): CI_Build =
      CI_Build(job.name, job.hosts.build_cluster, job.components.map(Component(_, "default")))

    def task(job: Build_CI.Job): Task =
      Task(CI_Build(job), job.hosts.hosts_spec, job.timeout, other_settings = job.other_settings,
        isabelle_rev = "default")
  }

  case class CI_Build(name: String, build_cluster: Boolean, extra_components: List[Component])
    extends Build_Config {
    def fresh_build: Boolean = true
    def command(job_url: Url, build_hosts: List[Build_Cluster.Host]): String =
      " build_ci" +
      " -u " + Bash.string(job_url.toString) +
      if_proper(build_cluster, build_hosts.map(host => " -H " + Bash.string(host.print)).mkString) +
      " " + name
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
    presentation: Boolean = false,
    verbose: Boolean = false
  ) extends Build_Config {
    def name: String = User_Build.name
    def extra_components: List[Component] = afp_rev.map(Component.afp).toList
    def build_cluster: Boolean = true
    def command(job_url: Url, build_hosts: List[Build_Cluster.Host]): String = {
      " build" +
        if_proper(afp_rev, " -A:") +
        base_sessions.map(session => " -B " + Bash.string(session)).mkString +
        build_hosts.map(host => " -H " + Bash.string(host.print)).mkString +
        if_proper(presentation, " -P:") +
        if_proper(requirements, " -R") +
        exclude_session_groups.map(session => " -X " + Bash.string(session)).mkString +
        if_proper(all_sessions, " -a") +
        if_proper(build_heap, " -b") +
        if_proper(clean_build, " -c") +
        if_proper(export_files, " -e") +
        if_proper(fresh_build, " -f") +
        session_groups.map(session => " -g " + Bash.string(session)).mkString +
        Options.Spec.bash_strings(prefs, bg = true) +
        if_proper(verbose, " -v") +
        exclude_sessions.map(session => " -x " + Bash.string(session)).mkString +
        sessions.map(session => " " + Bash.string(session)).mkString
    }
  }

  enum Priority { case low, normal, high }

  object Build {
    def name(kind: String, id: Long): String = kind + "/" + id
  }

  sealed trait Build extends Name.T

  sealed case class Task(
    build_config: Build_Config,
    hosts_spec: String,
    timeout: Time,
    other_settings: List[String] = Nil,
    uuid: UUID.T = UUID.random(),
    submit_date: Date = Date.now(),
    priority: Priority = Priority.normal,
    isabelle_rev: String = ""
  ) extends Build {
    def name: String = uuid.toString
    def kind: String = build_config.name
    def components: List[Component] = Component.isabelle(isabelle_rev) :: extra_components
    def extra_components: List[Component] = build_config.extra_components

    def build_cluster = build_config.build_cluster
    def build_hosts: List[Build_Cluster.Host] =
      Build_Cluster.Host.parse(Registry.global, hosts_spec)
  }

  sealed case class Job(
    uuid: UUID.T,
    kind: String,
    id: Long,
    build_cluster: Boolean,
    hostnames: List[String],
    components: List[Component],
    timeout: Time,
    start_date: Date = Date.now(),
    cancelled: Boolean = false
  ) extends Build { def name: String = Build.name(kind, id) }

  object Status {
    def from_result(result: Process_Result): Status = {
      if (result.ok) Status.ok
      else if (result.interrupted) Status.cancelled
      else Status.failed
    }
  }

  enum Status { case ok, cancelled, aborted, failed }

  sealed case class Result(
    kind: String,
    id: Long,
    status: Status,
    uuid: Option[UUID.T],
    build_host: String,
    start_date: Date,
    end_date: Option[Date],
    isabelle_version: Option[String],
    afp_version: Option[String],
    serial: Long = 0,
  ) extends Build {
    def name: String = Build.name(kind, id)
    def components: List[Component] =
      isabelle_version.map(Component.isabelle).toList ::: afp_version.map(Component.afp).toList
  }

  object State {
    def max_serial(serials: Iterable[Long]): Long = serials.maxOption.getOrElse(0L)
    def inc_serial(serial: Long): Long = {
      require(serial < Long.MaxValue, "number overflow")
      serial + 1
    }

    type Pending = Name.Data[Task]
    type Running = Name.Data[Job]
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

    def next(build_hosts: List[Build_Cluster.Host]): Option[Task] = {
      val cluster_running = running.values.exists(_.build_cluster)
      val available = build_hosts.map(_.hostname).toSet -- running.values.flatMap(_.hostnames).toSet
      val ready =
        for {
          (_, task) <- pending
          if !task.build_cluster || !cluster_running
          if task.build_hosts.map(_.hostname).forall(available.contains)
        } yield task

      if (ready.isEmpty) None
      else {
        val priority = ready.map(_.priority).maxBy(_.ordinal)
        ready.filter(_.priority == priority).toList.sortBy(_.submit_date)(Date.Ordering).headOption
      }
    }

    def add_running(job: Job): State = copy(running = running + (job.name -> job))
    def remove_running(name: String): State = copy(running = running - name)
    def cancel_running(name: String): State =
      running.get(name) match {
        case Some(job) => copy(running = (running - name) + (name -> job.copy(cancelled = true)))
        case None => this
      }

    def add_finished(result: Result): State = copy(finished = finished + (result.name -> result))

    lazy val kinds = (
      pending.values.map(_.kind) ++
      running.values.map(_.kind) ++
      finished.values.map(_.kind)).toList.distinct

    def next_id(kind: String): Long = {
      val serials = get_finished(kind).map(_.id) ::: get_running(kind).map(_.id)
      State.inc_serial(State.max_serial(serials))
    }

    def get_running(kind: String): List[Job] =
      (for ((_, job) <- running if job.kind == kind) yield job).toList

    def get_finished(kind: String): List[Result] =
      (for ((_, result) <- finished if result.kind == kind) yield result).toList

    def get(name: String): Option[Build] =
      pending.get(name).orElse(running.get(name)).orElse(finished.get(name))

    def get(uuid: UUID.T): Option[Build] =
      pending.values.find(_.uuid == uuid).orElse(
        running.values.find(_.uuid == uuid)).orElse(
        finished.values.find(_.uuid.contains(uuid)))
  }


  /** SQL data model **/

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
      val build_cluster = SQL.Column.bool("build_cluster")
      val hosts_spec = SQL.Column.string("hosts_spec")
      val timeout = SQL.Column.long("timeout")
      val other_settings = SQL.Column.string("other_settings")
      val uuid = SQL.Column.string("uuid").make_primary_key
      val submit_date = SQL.Column.date("submit_date")
      val priority = SQL.Column.string("priority")
      val isabelle_rev = SQL.Column.string("isabelle_rev")
      val extra_components = SQL.Column.string("extra_components")

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
      val verbose = SQL.Column.bool("verbose")

      val table =
        make_table(List(kind, build_cluster, hosts_spec, timeout, other_settings, uuid, submit_date,
          priority, isabelle_rev, extra_components, prefs, requirements, all_sessions,
          base_sessions, exclude_session_groups, exclude_sessions, session_groups, sessions,
          build_heap, clean_build, export_files, fresh_build, presentation, verbose),
        name = "pending")
    }

    def pull_pending(db: SQL.Database): Build_Manager.State.Pending =
      db.execute_query_statement(Pending.table.select(), Map.from[String, Task], get =
        { res =>
          val kind = res.string(Pending.kind)
          val build_cluster = res.bool(Pending.build_cluster)
          val hosts_spec = res.string(Pending.hosts_spec)
          val timeout = Time.ms(res.long(Pending.timeout))
          val other_settings = split_lines(res.string(Pending.other_settings))
          val uuid = res.string(Pending.uuid)
          val submit_date = res.date(Pending.submit_date)
          val priority = Priority.valueOf(res.string(Pending.priority))
          val isabelle_rev = res.string(Pending.isabelle_rev)
          val extra_components =
            space_explode(',', res.string(Pending.extra_components)).map(Component.parse)

          val build_config =
            if (kind != User_Build.name) CI_Build(kind, build_cluster, extra_components)
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
              val verbose = res.bool(Pending.verbose)

              val afp_rev = extra_components.find(_.name == Component.AFP).map(_.rev)
              User_Build(afp_rev, prefs, requirements, all_sessions, base_sessions,
                exclude_session_groups, exclude_sessions, session_groups, sessions, build_heap,
                clean_build, export_files, fresh_build, presentation, verbose)
            }

          val task = Task(build_config, hosts_spec, timeout, other_settings, UUID.make(uuid),
            submit_date, priority, isabelle_rev)

          task.name -> task
        })

    def update_pending(
      db: SQL.Database,
      old_pending: Build_Manager.State.Pending,
      pending: Build_Manager.State.Pending
    ): Update = {
      val update = Update.make(old_pending, pending)
      val delete = update.delete.map(old_pending(_).uuid.toString)

      if (update.deletes)
        db.execute_statement(Pending.table.delete(Pending.uuid.where_member(delete)))

      if (update.inserts) {
        db.execute_batch_statement(Pending.table.insert(), batch =
          for (name <- update.insert) yield { (stmt: SQL.Statement) =>
            val task = pending(name)
            stmt.string(1) = task.kind
            stmt.bool(2) = task.build_cluster
            stmt.string(3) = task.hosts_spec
            stmt.long(4) = task.timeout.ms
            stmt.string(5) = cat_lines(task.other_settings)
            stmt.string(6) = task.uuid.toString
            stmt.date(7) = task.submit_date
            stmt.string(8) = task.priority.toString
            stmt.string(9) = task.isabelle_rev
            stmt.string(10) = task.extra_components.mkString(",")

            def get[A](f: User_Build => A): Option[A] =
              task.build_config match {
                case user_build: User_Build => Some(f(user_build))
                case _ => None
              }

            stmt.string(11) = get(user_build => user_build.prefs.map(_.print).mkString(","))
            stmt.bool(12) = get(_.requirements)
            stmt.bool(13) = get(_.all_sessions)
            stmt.string(14) = get(_.base_sessions.mkString(","))
            stmt.string(15) = get(_.exclude_session_groups.mkString(","))
            stmt.string(16) = get(_.exclude_sessions.mkString(","))
            stmt.string(17) = get(_.session_groups.mkString(","))
            stmt.string(18) = get(_.sessions.mkString(","))
            stmt.bool(19) = get(_.build_heap)
            stmt.bool(20) = get(_.clean_build)
            stmt.bool(21) = get(_.export_files)
            stmt.bool(22) = get(_.fresh_build)
            stmt.bool(23) = get(_.presentation)
            stmt.bool(24) = get(_.verbose)
          })
      }

      update
    }


    /* running */

    object Running {
      val uuid = SQL.Column.string("uuid").make_primary_key
      val kind = SQL.Column.string("kind")
      val id = SQL.Column.long("id")
      val build_cluster = SQL.Column.bool("build_cluster")
      val hostnames = SQL.Column.string("hostnames")
      val components = SQL.Column.string("components")
      val timeout = SQL.Column.long("timeout")
      val start_date = SQL.Column.date("start_date")
      val cancelled = SQL.Column.bool("cancelled")

      val table =
        make_table(List(uuid, kind, id, build_cluster, hostnames, components, timeout, start_date,
          cancelled),
        name = "running")
    }

    def pull_running(db: SQL.Database): Build_Manager.State.Running =
      db.execute_query_statement(Running.table.select(), Map.from[String, Job], get =
        { res =>
          val uuid = res.string(Running.uuid)
          val kind = res.string(Running.kind)
          val id = res.long(Running.id)
          val build_cluster = res.bool(Running.build_cluster)
          val hostnames = space_explode(',', res.string(Running.hostnames))
          val components = space_explode(',', res.string(Running.components)).map(Component.parse)
          val timeout = Time.ms(res.long(Running.timeout))
          val start_date = res.date(Running.start_date)
          val cancelled = res.bool(Running.cancelled)

          val job = Job(UUID.make(uuid), kind, id, build_cluster, hostnames, components, timeout,
            start_date, cancelled)

          job.name -> job
        })

    def update_running(
      db: SQL.Database,
      old_running: Build_Manager.State.Running,
      running: Build_Manager.State.Running
    ): Update = {
      val update = Update.make(old_running, running)
      val delete = update.delete.map(old_running(_).uuid.toString)

      if (update.deletes)
        db.execute_statement(Running.table.delete(Running.uuid.where_member(delete)))

      if (update.inserts) {
        db.execute_batch_statement(Running.table.insert(), batch =
          for (name <- update.insert) yield { (stmt: SQL.Statement) =>
            val job = running(name)
            stmt.string(1) = job.uuid.toString
            stmt.string(2) = job.kind
            stmt.long(3) = job.id
            stmt.bool(4) = job.build_cluster
            stmt.string(5) = job.hostnames.mkString(",")
            stmt.string(6) = job.components.mkString(",")
            stmt.long(7) = job.timeout.ms
            stmt.date(8) = job.start_date
            stmt.bool(9) = job.cancelled
          })
      }
      update
    }


    /* finished */

    object Finished {
      val kind = SQL.Column.string("kind")
      val id = SQL.Column.long("id")
      val status = SQL.Column.string("status")
      val uuid = SQL.Column.string("uuid")
      val build_host = SQL.Column.string("build_host")
      val start_date = SQL.Column.date("start_date")
      val end_date = SQL.Column.date("end_date")
      val isabelle_version = SQL.Column.string("isabelle_version")
      val afp_version = SQL.Column.string("afp_version")
      val serial = SQL.Column.long("serial").make_primary_key

      val table =
        make_table(
          List(kind, id, status, uuid, build_host, start_date, end_date, isabelle_version,
            afp_version, serial),
          name = "finished")
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
          val id = res.long(Finished.id)
          val status = Status.valueOf(res.string(Finished.status))
          val uuid = res.get_string(Finished.uuid).map(UUID.make)
          val build_host = res.string(Finished.build_host)
          val start_date = res.date(Finished.start_date)
          val end_date = res.get_date(Finished.end_date)
          val isabelle_version = res.get_string(Finished.isabelle_version)
          val afp_version = res.get_string(Finished.afp_version)
          val serial = res.long(Finished.serial)

          val result = Result(kind, id, status, uuid, build_host, start_date, end_date,
            isabelle_version, afp_version, serial)
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
            stmt.long(2) = result.id
            stmt.string(3) = result.status.toString
            stmt.string(4) = result.uuid.map(_.toString)
            stmt.string(5) = result.build_host
            stmt.date(6) = result.start_date
            stmt.date(7) = result.end_date
            stmt.string(8) = result.isabelle_version
            stmt.string(9) = result.afp_version
            stmt.long(10) = result.serial
          })

      old ++ insert.map(result => result.serial.toString -> result)
    }
  }


  /** build reports **/

  object Report {
    case class Data(
      build_log: String,
      component_logs: List[(String, String)],
      component_diffs: List[(String, String)])
  }

  case class Report(kind: String, id: Long, dir: Path) {
    private val log_name = "build-manager"
    private val diff_ext = "diff"
    private val log_ext = "log"

    private def log_file = dir + Path.basic(log_name).log
    private def log_file_gz = dir + Path.basic(log_name).log.gz

    def init(): Unit = Isabelle_System.make_directory(dir)

    def ok: Boolean = log_file.is_file != log_file_gz.is_file

    def progress: Progress = new File_Progress(log_file)

    private def read_gz(file: Path, ext: String): Option[(String, String)] =
      if (!File.is_gz(file.file_name) || file.drop_ext.get_ext != ext) None
      else Some(file.drop_ext.drop_ext.file_name -> File.read_gzip(file))

    def read: Report.Data = {
      val build_log =
        if_proper(ok, if (log_file.is_file) File.read(log_file) else File.read_gzip(log_file_gz))

      val component_diffs =
        File.read_dir(dir).flatMap(name => read_gz(dir + Path.basic(name), diff_ext))
      val component_logs =
        File.read_dir(dir).flatMap(name => read_gz(dir + Path.basic(name), log_ext))

      Report.Data(build_log, component_logs, component_diffs)
    }

    def write_log(
      component: String,
      repository: Mercurial.Repository,
      rev0: String,
      rev: String
    ): Unit =
      if (rev0.nonEmpty && rev.nonEmpty && rev0 != rev) {
        val log_opts = "--graph --color always"
        val rev1 = "children(" + rev0 + ")"
        val cmd = repository.command_line("log", Mercurial.opt_rev(rev1 + ":" + rev), log_opts)
        val log = Isabelle_System.bash("export HGPLAINEXCEPT=color\n" + cmd).check.out
        if (log.nonEmpty) File.write_gzip(dir + Path.basic(component).ext(log_ext).gz, log)
      }

    def write_diff(
      component: String,
      repository: Mercurial.Repository,
      rev0: String,
      rev: String
    ): Unit =
      if (rev0.nonEmpty && rev.nonEmpty) {
        val diff_opts = "--noprefix --nodates --ignore-all-space --color always"
        val cmd = repository.command_line("diff", Mercurial.opt_rev(rev0 + ":" + rev), diff_opts)
        val diff = Isabelle_System.bash("export HGPLAINEXCEPT=color\n" + cmd).check.out
        if (diff.nonEmpty) File.write_gzip(dir + Path.basic(component).ext(diff_ext).gz, diff)
      }

    def result(uuid: Option[UUID.T]): Result = {
      val End = """^Job ended at [^,]+, with status (\w+)$""".r

      val build_log_file = Build_Log.Log_File(log_name, Library.trim_split_lines(read.build_log))

      val meta_info = build_log_file.parse_meta_info()
      val status =
        build_log_file.lines.last match {
          case End(status) => Status.valueOf(status)
          case _ => Status.aborted
        }
      val build_host = meta_info.get_build_host.getOrElse(error("No build host"))
      val start_date = meta_info.get_build_start.getOrElse(error("No start date"))
      val end_date = meta_info.get_build_end
      val isabelle_version = meta_info.get(Build_Log.Prop.isabelle_version)
      val afp_version = meta_info.get(Build_Log.Prop.afp_version)

      if (log_file.is_file) {
        File.write_gzip(log_file_gz, build_log_file.text)
        Isabelle_System.rm_tree(log_file)
      }

      Result(kind, id, status, uuid, build_host, start_date, end_date, isabelle_version,
        afp_version)
    }
  }


  /** running build manager processes **/

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
      process_futures: Map[String, Future[Build_Process]],
      result_futures: Map[String, Future[Process_Result]]
    ) {
      def is_empty = process_futures.isEmpty && result_futures.isEmpty

      def init(context: Context): State = {
        val process_future = Future.fork(Build_Process.open(context))
        val result_future =
          Future.fork(
            process_future.join_result match {
              case Exn.Res(process) => process.run()
              case Exn.Exn(exn) => Process_Result(Process_Result.RC.interrupt).error(exn.getMessage)
            })
        new State(
          process_futures + (context.name -> process_future),
          result_futures + (context.name -> result_future))
      }

      def running: List[String] = process_futures.keys.toList

      def update: (State, Map[String, Process_Result]) = {
        val finished =
          for ((name, future) <- result_futures if future.is_finished)
          yield name ->
            (future.join_result match {
              case Exn.Res(result) => result
              case Exn.Exn(exn) => Process_Result(Process_Result.RC.interrupt).error(exn.getMessage)
            })

        val process_futures1 = process_futures.filterNot((name, _) => finished.contains(name))
        val result_futures1 = result_futures.filterNot((name, _) => finished.contains(name))

        (new State(process_futures1, result_futures1), finished)
      }

      def cancel(cancelled: List[String]): State = {
        for (name <- cancelled) {
          val process_future = process_futures(name)
          if (process_future.is_finished) process_future.join.cancel()
          else process_future.cancel()
        }

        new State(process_futures.filterNot((name, _) => cancelled.contains(name)), result_futures)
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

    private def start_next(): Option[Context] =
      synchronized_database("start_next") {
        for ((name, task) <- _state.pending if Exn.is_exn(Exn.capture(task.build_hosts))) {
          progress.echo("Invalid host spec for task " + name + ": " + quote(task.hosts_spec))
          _state = _state.remove_pending(name)
        }

        _state.next(build_hosts).flatMap { task =>
          echo("Initializing " + task.name)

          _state = _state.remove_pending(task.name)

          val id = _state.next_id(task.kind)
          val context = Context(store, task, id)

          val start_date = Date.now()

          val start_msg =
            "Starting job " + Build.name(task.kind, id) +
            " at " + Build_Log.print_date(start_date) + "," +
            " on " + (
              if (task.build_cluster) "cluster"
              else Library.the_single(task.build_hosts).hostname)

          echo(start_msg + " (id " + task.uuid + ")")

          Exn.capture {
            context.report.init()
            context.report.progress.echo(start_msg)

            store.sync_permissions(context.task_dir)

            val isabelle_rev = sync(isabelle_repository, task.isabelle_rev, context.task_dir)

            val hostnames = task.build_hosts.map(_.hostname).distinct

            val extra_components =
              for (extra_component <- task.extra_components)
              yield sync_dirs.find(_.name == extra_component.name) match {
                case Some(sync_dir) =>
                  val target = context.task_dir + sync_dir.target
                  val rev = sync(sync_dir.hg, extra_component.rev, target)

                  if (!extra_component.is_local)
                    File.append(context.task_dir + Sync.DIRS_ROOTS, sync_dir.roots_entry + "\n")
                  extra_component.copy(rev = rev)
                case None =>
                  if (extra_component.is_local) extra_component
                  else error("Unknown component " + extra_component)
              }

            if (task.kind != User_Build.name && _state.get_finished(task.kind).nonEmpty) {
              val previous = _state.get_finished(task.kind).maxBy(_.id)

              for (isabelle_rev0 <- previous.isabelle_version) {
                context.report.write_log(Component.Isabelle,
                  isabelle_repository, isabelle_rev0, isabelle_rev)
                context.report.write_diff(Component.Isabelle,
                  isabelle_repository, isabelle_rev0, isabelle_rev)
              }

              for {
                afp_rev0 <- previous.afp_version
                afp <- extra_components.find(_.name == Component.AFP)
                sync_dir <- sync_dirs.find(_.name == afp.name)
              } {
                context.report.write_log(afp.name, sync_dir.hg, afp_rev0, afp.rev)
                context.report.write_diff(afp.name, sync_dir.hg, afp_rev0, afp.rev)
              }
            }

            Job(task.uuid, task.kind, id, task.build_cluster, hostnames,
              Component.isabelle(isabelle_rev) :: extra_components, task.timeout, start_date)
          } match {
            case Exn.Res(job) =>
              _state = _state.add_running(job)

              for (component <- job.components)
                context.report.progress.echo("Using " + component.toString)

              Some(context)
            case Exn.Exn(exn) =>
              context.report.progress.echo_error_message("Failed to start job: " + exn.getMessage)
              echo_error_message("Failed to start " + task.uuid + ": " + exn.getMessage)

              Isabelle_System.rm_tree(context.task_dir)

              _state = _state.add_finished(context.report.result(Some(task.uuid)))

              None
          }
        }
      }

    private def stop_cancelled(state: Runner.State): Runner.State =
      synchronized_database("stop_cancelled") {
        val now = Date.now()
        for {
          name <- state.running
          job = _state.running(name)
          if now - job.start_date > job.timeout
        } {
          _state = _state.cancel_running(name)

          val timeout_msg = "Timeout after " + job.timeout.message_hms
          store.report(job.kind, job.id).progress.echo_error_message(timeout_msg)
          echo(job.name + ": " + timeout_msg)
        }

        val cancelled = for (name <- state.running if _state.running(name).cancelled) yield name
        state.cancel(cancelled)
      }

    private def finish_job(name: String, process_result: Process_Result): Unit =
      synchronized_database("finish_job") {
        val job = _state.running(name)

        val end_date = Date.now()
        val status = Status.from_result(process_result)
        val end_msg = "Job ended at " + Build_Log.print_date(end_date) + ", with status " + status

        val report = store.report(job.kind, job.id)
        report.progress.echo(end_msg)

        val interrupted_error = process_result.interrupted && process_result.err.nonEmpty
        val err_msg = if_proper(interrupted_error, ": " + process_result.err)
        echo(end_msg + " (code " + process_result.rc + ")" + err_msg)

        _state = _state
          .remove_running(job.name)
          .add_finished(report.result(Some(job.uuid)))
      }

    override def stopped(state: Runner.State): Boolean = progress.stopped && state.is_empty

    def init: Runner.State = Runner.State.empty
    def loop_body(state: Runner.State): Runner.State = {
      val state1 =
        if (progress.stopped) state
        else {
          start_next() match {
            case None => state
            case Some(context) => state.init(context)
          }
        }
      val state2 = stop_cancelled(state1)
      val (state3, results) = state2.update
      results.foreach(finish_job)
      state3
    }
  }


  /* repository poller */

  object Poller {
    case class State(current: List[Component], next: Future[List[Component]])
  }

  class Poller(
    ci_jobs: List[Build_CI.Job],
    store: Store,
    isabelle_repository: Mercurial.Repository,
    sync_dirs: List[Sync.Dir],
    progress: Progress
  ) extends Loop_Process[Poller.State]("Poller", store, progress) {

    override def delay = options.seconds("build_manager_poll_delay")

    private def current: List[Component] =
      Component.isabelle(isabelle_repository.id("default")) ::
        sync_dirs.map(dir => Component(dir.name, dir.hg.id("default")))

    private def poll: Future[List[Component]] = Future.fork {
      Par_List.map((repo: Mercurial.Repository) => repo.pull(),
        isabelle_repository :: sync_dirs.map(_.hg))

      current
    }

    val init: Poller.State = Poller.State(current, poll)

    private def add_tasks(current: List[Component], next: List[Component]): Unit = {
      val updated_components = next.zip(current).filter(_ != _).map(_._1.name).toSet

      synchronized_database("add_tasks") {
        for {
          ci_job <- ci_jobs
          if ci_job.trigger == Build_CI.On_Commit
          if (Component.Isabelle :: ci_job.components).exists(updated_components.contains)
          if !_state.pending.values.exists(_.kind == ci_job.name)
        } _state = _state.add_pending(CI_Build.task(ci_job))
      }
    }

    def loop_body(state: Poller.State): Poller.State =
      if (!state.next.is_finished) state
      else {
        state.next.join_result match {
          case Exn.Exn(exn) =>
            echo_error_message("Could not reach repository: " + exn.getMessage)
            Poller.State(state.current, poll)
          case Exn.Res(next) =>
            if (state.current != next) {
              echo("Found new revisions: " + next)
              add_tasks(state.current, next)
            }
            Poller.State(next, poll)
        }
      }
  }

  class Timer(
    ci_jobs: List[Build_CI.Job],
    store: Store,
    isabelle_repository: Mercurial.Repository,
    sync_dirs: List[Sync.Dir],
    progress: Progress
  ) extends Loop_Process[Date]("Timer", store, progress) {

    override def delay = options.seconds("build_manager_timer_delay")

    private def add_tasks(previous: Date, next: Date): Unit = synchronized_database("add_tasks") {
      for (ci_job <- ci_jobs)
        ci_job.trigger match {
          case Build_CI.Timed(in_interval) if in_interval(previous, next) =>
            val task = CI_Build.task(ci_job)
            echo("Triggered task " + task.kind)
            _state = _state.add_pending(task)
          case _ =>
        }
    }

    def init: Date = Date.now()
    def loop_body(previous: Date): Date = {
      val now = Date.now()
      add_tasks(previous, now)
      now
    }
  }


  /* web server */

  object Web_Server {
    val Id = new Properties.String(Markup.ID)

    object Page {
      val HOME = Path.basic("home")
      val OVERVIEW = Path.basic("overview")
      val BUILD = Path.basic("build")
      val DIFF = Path.basic("diff")
    }

    def paths(store: Store): Web_App.Paths =
      Web_App.Paths(store.address, Path.current, serve_frontend = true, landing = Page.HOME)

    object API {
      val BUILD_CANCEL = Path.explode("api/build/cancel")
    }

    object Cache {
      def empty: Cache = new Cache()
    }

    class Cache private(keep: Time = Time.minutes(1)) {
      private var cached: Map[Report, (Time, Report.Data)] = Map.empty

      def update(): Unit = synchronized {
        cached =
          for {
            (report, (time, _)) <- cached
            if time + keep > Time.now()
          } yield report -> (time, report.read)
      }

      def lookup(report: Report): Report.Data = synchronized {
        cached.get(report) match {
          case Some((_, data)) =>
            cached += report -> (Time.now(), data)
          case None =>
            cached += report -> (Time.now(), report.read)
        }
        cached(report)._2
      }
    }
  }

  class Web_Server(port: Int, store: Store, progress: Progress)
    extends Loop_Process[Unit]("Web_Server", store, progress) {
    import Web_App.*
    import Web_Server.*

    val paths = Web_Server.paths(store)
    val cache = Cache.empty

    enum Model {
      case Error extends Model
      case Cancelled extends Model
      case Home(state: State) extends Model
      case Overview(kind: String, state: State) extends Model
      case Details(build: Build, state: State, public: Boolean = true) extends Model
      case Diff(build: Build, state: State) extends Model
    }

    object View {
      import HTML.*
      import More_HTML.*

      def render_if(cond: Boolean, body: XML.Body): XML.Body = if (cond) body else Nil

      def page_link(path: Path, s: String, props: Properties.T = Nil): XML.Elem =
        link(paths.frontend_url(path, props).toString, text(s)) + ("target" -> "_parent")

      def link_build(name: String, id: Long): XML.Elem =
        page_link(Page.BUILD, "#" + id, Markup.Name(name))

      private def render_page(name: String)(body: => XML.Body): XML.Body = {
        def nav_link(path: Path, s: String): XML.Elem = page_link(Page.HOME, "Home")

        More_HTML.header(List(nav(List(nav_link(Page.HOME, "home"))))) ::
        main(chapter(name) :: body ::: Nil) :: Nil
      }

      private def summary(start: Date): XML.Body =
        text(" running since " + Build_Log.print_date(start))

      private def summary(status: Status, start: Date, end: Option[Date]): XML.Body =
        text(" (" + status.toString + if_proper(end, " in " + (end.get - start).message_hms) +
          ") on " + Build_Log.print_date(start))

      def render_home(state: State): XML.Body = render_page("Dashboard") {
        def render_kind(kind: String): XML.Elem = {
          val running = state.get_running(kind).sortBy(_.id).reverse
          val finished = state.get_finished(kind).sortBy(_.id).reverse

          def render_previous(finished: List[Result]): XML.Body = {
            val (failed, rest) = finished.span(_.status != Status.ok)
            val first_failed = failed.lastOption.map(result =>
              par(
                text("first failure: ") ::: link_build(result.name, result.id) ::
                summary(result.status, result.start_date, result.end_date)))
            val last_success = rest.headOption.map(result =>
              par(
                text("last success: ") ::: link_build(result.name, result.id) ::
                summary(result.status, result.start_date, result.end_date)))
            first_failed.toList ::: last_success.toList
          }

          def render_job(job: Job): XML.Body =
            par(link_build(job.name, job.id) :: summary(job.start_date)) ::
            render_if(
              finished.headOption.exists(_.status != Status.ok) && job.kind != User_Build.name,
              render_previous(finished))

          def render_result(result: Result): XML.Body =
            par(
              link_build(result.name, result.id) ::
              summary(result.status, result.start_date, result.end_date)) ::
            render_if(result.status != Status.ok && result.kind != User_Build.name,
              render_previous(finished.tail))

          fieldset(
            XML.elem("legend", List(page_link(Page.OVERVIEW, kind, Markup.Kind(kind)))) ::
            (if (running.nonEmpty) render_job(running.head)
            else if (finished.nonEmpty) render_result(finished.head)
            else Nil))
        }

        text("Queue: " + state.pending.size + " tasks waiting") :::
        section("Builds") :: par(text("Total: " + state.num_builds + " builds")) ::
        state.kinds.sorted.map(render_kind)
      }

      def render_overview(kind: String, state: State): XML.Body =
        render_page("Overview: " + kind + " job ") {
          def render_job(job: Job): XML.Body =
            List(par(link_build(job.name, job.id) :: summary(job.start_date)))

          def render_result(result: Result): XML.Body =
            List(par(
              link_build(result.name, result.id) ::
              summary(result.status, result.start_date, result.end_date)))

          itemize(
            state.get_running(kind).sortBy(_.id).reverse.map(render_job) :::
            state.get_finished(kind).sortBy(_.id).reverse.map(render_result)) :: Nil
        }

      private val ID = Params.key(Markup.ID)

      def render_details(build: Build, state: State, public: Boolean): XML.Body =
        render_page("Build: " + build.name) {
          def render_cancel(uuid: UUID.T): XML.Body =
            render_if(!public, List(
              submit_form("", List(hidden(ID, uuid.toString),
                api_button(paths.api_route(API.BUILD_CANCEL), "cancel build")))))

          def render_rev(components: List[Component], data: Report.Data): XML.Body = {
            val hg_info = data.component_logs.map(_._1) ++ data.component_diffs.map(_._1)
            val s = components.mkString(", ")

            if (!components.map(_.name).exists(hg_info.toSet)) text("Components: " + s)
            else text("Components: ") :+ page_link(Page.DIFF, s, Markup.Name(build.name))
          }

          build match {
            case task: Task =>
              par(text("Task from " + Build_Log.print_date(task.submit_date) + ". ")) ::
              par(text(task.components.mkString(", "))) ::
              render_cancel(task.uuid)

            case job: Job =>
              val report_data = cache.lookup(store.report(job.kind, job.id))

              par(text("Start: " + Build_Log.print_date(job.start_date))) ::
              par(
                if (job.cancelled) text("Cancelling ...")
                else text("Running ...") ::: render_cancel(job.uuid)) ::
              par(render_rev(job.components, report_data)) ::
              par(List(source(report_data.build_log))) :: Nil

            case result: Result =>
              val report_data = cache.lookup(store.report(result.kind, result.id))

              par(text("Start: " + Build_Log.print_date(result.start_date) +
                if_proper(result.end_date,
                  ", took " + (result.end_date.get - result.start_date).message_hms))) ::
              par(text("Status: " + result.status)) ::
              par(render_rev(result.components, report_data)) ::
              par(List(source(report_data.build_log))) :: Nil
          }
        }

      def render_diff(build: Build, state: State): XML.Body = render_page("Diff: " + build.name) {
        def colored(s: String): XML.Body = {
          val Colored = "([^\u001b]*)\u001b\\[([0-9;]+)m(.*)\u001b\\[0m([^\u001b]*)".r
          val colors = List("black", "maroon", "green", "olive", "navy", "purple", "teal", "silver")

          val lines = split_lines(s).map {
            case Colored(pre, code, s, post) =>
              val codes = space_explode(';', code.stripSuffix(";1")).map(Value.Int.parse)
              val fg = codes match { case 0 :: i :: Nil => colors.unapply(i - 30) case _ => None }

              val sp = span(if (code.endsWith(";1")) List(bold(text(s))) else text(s))
              val sp1 = fg.map(color => sp + ("style" -> ("color:" + color))).getOrElse(sp)
              List(span(text(pre)), sp1, span(text(post)))
            case line => text(Library.strip_ansi_color(line))
          }

          List(source(Library.separate(nl, lines).flatten))
        }

        def render_diff(data: Report.Data, components: List[Component]): XML.Body =
          par(List(page_link(Page.BUILD, "back to build", Markup.Name(build.name)))) ::
          (for (component <- components if !component.is_local) yield {
            val infos = 
              data.component_logs.toMap.get(component.name).toList.flatMap(colored) :::
              data.component_diffs.toMap.get(component.name).toList.flatMap(colored)

            val header = if (infos.isEmpty) component.toString else component.name + ":"
            par(subsubsection(header) :: infos)
          })

        build match {
          case job: Job =>
            render_diff(cache.lookup(store.report(job.kind, job.id)), job.components)
          case result: Result =>
            render_diff(cache.lookup(store.report(result.kind, result.id)), result.components)
          case _ => Nil
        }
      }

      def render_cancelled: XML.Body =
        render_page("Build cancelled")(List(page_link(Page.HOME, "Home")))

      def parse_uuid(params: Params.Data): Option[UUID.T] =
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

      def get_build(props: Properties.T): Option[Model.Details] =
        props match {
          case Markup.Name(name) =>
            val state = _state
            state.get(name).map(Model.Details(_, state))
          case Web_Server.Id(UUID(uuid)) =>
            val state = _state
            state.get(uuid).map(Model.Details(_, state, public = false))
          case _ => None
        }

      def get_diff(props: Properties.T): Option[Model.Diff] =
        props match {
          case Markup.Name(name) =>
            val state = _state
            state.get(name).map(Model.Diff(_, state))
          case _ => None
        }

      def cancel_build(params: Params.Data): Option[Model] =
        for {
          uuid <- View.parse_uuid(params)
          model <-
            synchronized_database("cancel_build") {
              _state.get(uuid).map {
                case task: Task =>
                  _state = _state.remove_pending(task.name)
                  Model.Cancelled
                case job: Job =>
                  _state = _state.cancel_running(job.name)
                  Model.Cancelled
                case result: Result => Model.Details(result, _state, public = false)
              }
            }
        } yield model

      def render(model: Model): XML.Body =
        HTML.title("Isabelle Build Manager") :: (
          model match {
            case Model.Error => HTML.text("invalid request")
            case Model.Home(state) => View.render_home(state)
            case Model.Overview(kind, state) => View.render_overview(kind, state)
            case Model.Details(build, state, public) => View.render_details(build, state, public)
            case Model.Diff(build, state) => View.render_diff(build, state)
            case Model.Cancelled => View.render_cancelled
          })

      val error_model: Model = Model.Error
      val endpoints = List(
        Get(Page.HOME, "home", _ => overview),
        Get(Page.OVERVIEW, "overview", get_overview),
        Get(Page.BUILD, "build", get_build),
        Get(Page.DIFF, "diff", get_diff),
        Post(API.BUILD_CANCEL, "cancel build", cancel_build))
      val logo = Bytes.read(Path.explode("$ISABELLE_HOME/lib/logo/isabelle_transparent-48.gif"))
      val head =
        List(
          HTML.title("Isabelle Build Manager"),
          Web_App.More_HTML.icon("data:image/x-icon;base64," + logo.encode_base64.text),
          HTML.style_file("https://hawkz.github.io/gdcss/gd.css"),
          HTML.style("html { background-color: white; }"))
    }

    def init: Unit = server.start()
    def loop_body(u: Unit): Unit = {
      if (progress.stopped) server.stop()
      else synchronized_database("iterate") { cache.update() }
    }
  }


  /** context **/

  case class Context(store: Store, task: Task, id: Long) {
    def name = Build.name(task.kind, id)
    def report: Report = store.report(task.kind, id)
    def task_dir: Path = store.task_dir(task)

    def isabelle_identifier: String =
      if (task.build_cluster) store.options.string("build_cluster_identifier") else store.identifier

    def open_ssh(): SSH.System = {
      if (task.build_cluster) store.open_ssh()
      else Library.the_single(task.build_hosts).open_ssh(store.options)
    }
  }


  /** build process **/

  object Build_Process {
    def open(context: Context): Build_Process = new Build_Process(context.open_ssh(), context)
  }

  class Build_Process(ssh: SSH.System, context: Context) {
    private val task = context.task
    private val progress = context.report.progress


    /* resources with cleanup operations */

    private val _dir = ssh.tmp_dir()
    private val _isabelle =
      try {
        val rsync_context = Rsync.Context(ssh = ssh)
        val source = File.standard_path(context.task_dir)
        Rsync.exec(rsync_context, clean = true, args = List("--", Url.direct_path(source),
          rsync_context.target(_dir))).check

        Isabelle_System.rm_tree(context.task_dir)
        Other_Isabelle(_dir, context.isabelle_identifier, ssh, progress)
      }
      catch { case exn: Throwable => close(); throw exn }

    private val _process =
      try {
        val init_components =
          for {
            extra_component <- task.build_config.extra_components
            target = _dir + Sync.DIRS + Path.basic(extra_component.name)
            if Components.is_component_dir(target)
          } yield "init_component " + quote(target.absolute.implode)

        _isabelle.init(
          other_settings = _isabelle.init_components() ::: init_components ::: task.other_settings,
          fresh = task.build_config.fresh_build, echo = true)

        val paths = Web_Server.paths(context.store)
        val job_url = paths.frontend_url(Web_Server.Page.BUILD, Markup.Name(context.name))
        val cmd = task.build_config.command(job_url, task.build_hosts)
        progress.echo("isabelle" + cmd)

        val script = File.bash_path(Isabelle_Tool.exe(_isabelle.isabelle_home)) + cmd
        ssh.bash_process(_isabelle.bash_context(script), settings = false)
      }
      catch { case exn: Throwable => close(); throw exn }

    def cancel(): Unit = Option(_process).foreach(_.interrupt())

    def close(): Unit = {
      Option(_dir).foreach(ssh.rm_tree)
      Isabelle_System.rm_tree(context.task_dir)
      ssh.close()
    }


    /* execution */

    def run(): Process_Result = {
      val process_result =
        _process.result(progress_stdout = progress.echo(_), progress_stderr = progress.echo(_))
      close()
      process_result
    }
  }


  /** build manager store **/

  case class Store(options: Options) {
    val base_dir = Path.explode(options.string("build_manager_dir"))
    val identifier = options.string("build_manager_identifier")
    val address = Url(options.string("build_manager_address"))

    val pending = base_dir + Path.basic("pending")
    val finished = base_dir + Path.basic("finished")

    def task_dir(task: Task) = pending + Path.basic(task.uuid.toString)
    def report(kind: String, id: Long): Report =
      Report(kind, id, finished + Path.make(List(kind, id.toString)))

    def sync_permissions(dir: Path, ssh: SSH.System = SSH.Local): Unit = {
      ssh.execute("chmod -R g+rwx " + File.bash_path(dir))
      ssh.execute("chown -R :" + ssh_group + " " + File.bash_path(dir))
    }

    def init_dirs(): Unit =
      List(pending, finished).foreach(dir => sync_permissions(Isabelle_System.make_directory(dir)))

    val ssh_group: String = options.string("build_manager_ssh_group")

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


  /** build manager server **/

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
    val ci_jobs = space_explode(',', options.string("build_manager_ci_jobs")).map(Build_CI.the_job)

    progress.echo_if(ci_jobs.nonEmpty, "Managing ci jobs: " + commas_quote(ci_jobs.map(_.name)))

    using(store.open_database())(db =>
      Build_Manager.private_data.transaction_lock(db,
        create = true, label = "Build_Manager.build_manager") { store.init_dirs() })

    val processes = List(
      new Runner(store, build_hosts, isabelle_repository, sync_dirs, progress),
      new Poller(ci_jobs, store, isabelle_repository, sync_dirs, progress),
      new Timer(ci_jobs, store, isabelle_repository, sync_dirs, progress),
      new Web_Server(port, store, progress))

    val threads = processes.map(Isabelle_Thread.create(_))
    POSIX_Interrupt.handler {
      progress.stop()
      processes.foreach(_.interrupt())
    } {
      threads.foreach(_.start())
      threads.foreach(_.join())
    }
  }


  /* Isabelle tool wrapper */

  private def show_options(relevant_options: List[String], options: Options): String =
    cat_lines(relevant_options.flatMap(options.get).map(_.print))

  private val notable_server_options =
    List(
      "build_manager_dir",
      "build_manager_address",
      "build_manager_ssh_host",
      "build_manager_ssh_group",
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
    -H HOSTS     host specifications for all available hosts of the form
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


  /** restore build manager database **/

  def build_manager_database(
    options: Options,
    sync_dirs: List[Sync.Dir] = Sync.afp_dirs(),
    update_reports: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    val store = Store(options)
    using(store.open_database()) { db =>
      db.transaction {
        val tables0 = Build_Manager.private_data.tables.list
        val tables = tables0.filter(t => db.exists_table(t.name))
        if (tables.nonEmpty) {
          progress.echo("Removing tables " + commas_quote(tables.map(_.name)) + " ...")
          db.execute_statement(SQL.MULTI(tables.map(db.destroy)))
        }
      }

      val reports =
        for {
          kind <- File.read_dir(store.finished)
          entry <- File.read_dir(store.finished + Path.basic(kind))
          id <- Value.Long.unapply(entry)
          report = store.report(kind, id)
          if report.ok
        } yield report

      val results = reports.map(report => report -> report.result(None))

      if (update_reports) {
        val isabelle_repository = Mercurial.self_repository()
        val afp_repository =
          sync_dirs.find(_.name == Component.AFP).getOrElse(error("Missing AFP for udpate")).hg

        isabelle_repository.pull()
        afp_repository.pull()

        for ((kind, results0) <- results.groupBy(_._1.kind) if kind != User_Build.name) {
          val results1 = results0.sortBy(_._1.id)
          results1.foldLeft(("", "")) {
            case ((isabelle_rev0, afp_rev0), (report, result)) =>
              val isabelle_rev = result.isabelle_version.getOrElse("")
              val afp_rev = result.afp_version.getOrElse("")

              report.write_log(Component.Isabelle, isabelle_repository, isabelle_rev0, isabelle_rev)
              report.write_log(Component.AFP, afp_repository, afp_rev0, afp_rev)
              report.write_diff(
                Component.Isabelle, isabelle_repository, isabelle_rev0, isabelle_rev)
              report.write_diff(Component.AFP, afp_repository, afp_rev0, afp_rev)

              (isabelle_rev, afp_rev)
          }
        }
      }

      val state = State(finished = results.map((_, result) => result.name -> result).toMap)

      Build_Manager.private_data.transaction_lock(db,
        create = true, label = "Build_Manager.build_manager_database") {

        progress.echo("Writing " + results.length + " results ...")
        Build_Manager.private_data.push_state(db, State(), state)
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool1 = Isabelle_Tool("build_manager_database",
    "restore build_manager database from log files",
    Scala_Project.here,
    { args =>
      var afp_root: Option[Path] = None
      var options = Options.init()
      var update_reports = false

      val getopts = Getopts("""
Usage: isabelle build_manager_database [OPTIONS]

  Options are:
    -A ROOT      include AFP with given root directory (":" for """ + AFP.BASE.implode + """)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -u           update reports

  Restore build_manager database from log files.
""",
        "A:" -> (arg => afp_root = Some(if (arg == ":") AFP.BASE else Path.explode(arg))),
        "o:" -> (arg => options = options + arg),
        "u" -> (_ => update_reports = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      build_manager_database(options, sync_dirs = Sync.afp_dirs(afp_root),
        update_reports = update_reports, progress = progress)
    })


  /** build manager client */

  /* build task */

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
    verbose: Boolean = false,
    rev: String = "",
    progress: Progress = new Progress
  ): UUID.T = {
    val uuid = UUID.random()
    val afp_rev = if (afp_root.nonEmpty) Some("") else None

    val hosts_spec = options.string("build_manager_cluster")
    val timeout = options.seconds("build_manager_timeout")
    val paths = Web_Server.paths(store)

    val build_config = User_Build(afp_rev, prefs, requirements, all_sessions,
      base_sessions, exclude_session_groups, exclude_sessions, session_groups, sessions, build_heap,
      clean_build, export_files, fresh_build, presentation, verbose)
    val task = Task(build_config, hosts_spec, timeout, uuid = uuid, priority = Priority.high)

    val dir = store.task_dir(task)

    progress.interrupt_handler {
      using(store.open_ssh()) { ssh =>
        val rsync_context = Rsync.Context(ssh = ssh)
        progress.echo("Transferring repositories ...")
        Sync.sync(store.options, rsync_context, dir, preserve_jars = true,
          dirs = Sync.afp_dirs(afp_root), rev = rev)
        store.sync_permissions(dir, ssh)

        if (progress.stopped) {
          progress.echo("Cancelling submission ...")
          ssh.rm_tree(dir)
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

          val address = paths.frontend_url(Web_Server.Page.BUILD, Web_Server.Id(task.uuid.toString))
          progress.echo("Submitted task. Private url: " + address)
        }
      }
    }

    uuid
  }


  /* Isabelle tool wrapper */

  val notable_client_options = List("build_manager_ssh_user", "build_manager_ssh_group")

  val isabelle_tool2 = Isabelle_Tool("build_task", "submit build task for build manager",
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
      val prefs = new mutable.ListBuffer[Options.Spec]
      var verbose = false
      var rev = ""
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
    -p OPTION    override Isabelle system OPTION for build process (via NAME=VAL or NAME)
    -r REV       explicit revision (default: state of working directory)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Submit build task on SSH server. Notable system options:

""" + Library.indent_lines(2, show_options(notable_client_options, options)) + "\n",
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
        "p:" -> (arg => prefs += Options.Spec.make(arg)),
        "r:" -> (arg => rev = arg),
        "v" -> (_ => verbose = true),
        "x:" -> (arg => exclude_sessions += arg))

      val sessions = getopts(args)
      val store = Store(options)
      val progress = new Console_Progress()

      build_task(options, store, afp_root = afp_root, base_sessions = base_sessions.toList,
        presentation = presentation, requirements = requirements, exclude_session_groups =
        exclude_session_groups.toList, all_sessions = all_sessions, build_heap = build_heap,
        clean_build = clean_build, export_files = export_files, fresh_build = fresh_build,
        session_groups = session_groups.toList, sessions = sessions, prefs = prefs.toList, verbose =
        verbose, rev = rev, exclude_sessions = exclude_sessions.toList, progress = progress)
    })
}
