/*  Title:      Pure/Tools/build_cluster.scala
    Author:     Makarius

Management of build cluster: independent ssh hosts with access to shared
PostgreSQL server.

NB: extensible classes allow quite different implementations in user-space,
via the service class Build.Engine and overridable methods
Build.Engine.open_build_process(), Build_Process.open_build_cluster().
*/

package isabelle


object Build_Cluster {
  /* host specifications */

  object Host {
    private val rfc822_specials = """()<>@,;:\"[]"""

    private val HOSTNAME = "hostname"
    private val USER = "user"
    private val PORT = "port"
    private val JOBS = "jobs"
    private val NUMA = "numa"
    private val DIRS = "dirs"
    private val SHARED = "shared"

    val parameters: Options =
      Options.inline("""
        option hostname : string = "" -- "explicit SSH hostname"
        option user : string = ""     -- "explicit SSH user"
        option port : int = 0         -- "explicit SSH port"
        option jobs : int = 1         -- "maximum number of parallel jobs"
        option numa : bool = false    -- "cyclic shuffling of NUMA CPU nodes"
        option dirs : string = ""     -- "additional session directories (separated by colon)"
        option shared : bool = false  -- "shared directory: omit sync + init"
      """)

    def is_parameter(spec: Options.Spec): Boolean = parameters.defined(spec.name)

    lazy val test_options: Options = Options.init0()

    def apply(
      name: String = "",
      hostname: String = parameters.string(HOSTNAME),
      user: String = parameters.string(USER),
      port: Int = parameters.int(PORT),
      jobs: Int = parameters.int(JOBS),
      numa: Boolean = parameters.bool(NUMA),
      dirs: String = parameters.string(DIRS),
      shared: Boolean = parameters.bool(SHARED),
      options: List[Options.Spec] = Nil
    ): Host = {
      Path.split(dirs)  // check
      new Host(name, hostname, user, port, jobs, numa, dirs, shared, options)
    }

    def parse(str: String): List[Host] = {
      val names = str.takeWhile(c => !rfc822_specials.contains(c) || c == ',')
      val (params, options) =
        try {
          val rest = {
            val n = str.length
            val m = names.length
            val l =
              if (m == n) n
              else if (str(m) == ':') m + 1
              else error("Missing \":\" after host name")
            str.substring(l)
          }
          val (specs1, specs2) = Options.Spec.parse(rest).partition(is_parameter)
          (parameters ++ specs1, { test_options ++ specs2; specs2 })
        }
        catch {
          case ERROR(msg) =>
            cat_error(msg, "The error(s) above occurred in host specification " + quote(str))
        }
      for (name <- space_explode(',', names)) yield {
        apply(name = name,
          hostname = params.string(HOSTNAME),
          user = params.string(USER),
          port = params.int(PORT),
          jobs = params.int(JOBS),
          numa = params.bool(NUMA),
          dirs = params.string(DIRS),
          shared = params.bool(SHARED),
          options = options)
      }
    }
  }

  class Host(
    val name: String,
    val hostname: String,
    val user: String,
    val port: Int,
    val jobs: Int,
    val numa: Boolean,
    val dirs: String,
    val shared: Boolean,
    val options: List[Options.Spec]
  ) {
    host =>

    def ssh_host: String = proper_string(hostname) getOrElse name
    def is_local: Boolean = SSH.is_local(ssh_host)

    override def toString: String = print

    def print: String = {
      val params =
        List(
          if (host.hostname.isEmpty) "" else Options.Spec.print(Host.HOSTNAME, host.hostname),
          if (host.user.isEmpty) "" else Options.Spec.print(Host.USER, host.user),
          if (host.port == 0) "" else Options.Spec.print(Host.PORT, host.port.toString),
          if (host.jobs == 1) "" else Options.Spec.print(Host.JOBS, host.jobs.toString),
          if_proper(host.numa, Host.NUMA),
          if_proper(dirs, Options.Spec.print(Host.DIRS, host.dirs)),
          if_proper(host.shared, Host.SHARED)
        ).filter(_.nonEmpty)
      val rest = (params ::: host.options.map(_.print)).mkString(",")

      SSH.print_local(host.name) + if_proper(rest, ":" + rest)
    }

    def message(msg: String): String = "Host " + quote(host.name) + if_proper(msg, ": " + msg)

    def open_ssh(options: Options): SSH.System =
      SSH.open_system(options ++ host.options, ssh_host, port = host.port, user = host.user)

    def open_session(build_context: Build.Context, progress: Progress = new Progress): Session = {
      val ssh_options = build_context.build_options ++ host.options
      val ssh = open_ssh(build_context.build_options)
      new Session(build_context, host, ssh_options, ssh, progress)
    }
  }


  /* SSH sessions */

  class Session(
    val build_context: Build.Context,
    val host: Host,
    val options: Options,
    val ssh: SSH.System,
    val progress: Progress
  ) extends AutoCloseable {
    override def toString: String = ssh.toString

    val remote_identifier: String = options.string("build_cluster_identifier")
    val remote_root: Path = Path.explode(options.string("build_cluster_root"))
    val remote_isabelle_home: Path = remote_root + Path.explode("isabelle")
    val remote_afp_root: Option[Path] =
      if (build_context.afp_root.isEmpty) None
      else Some(remote_isabelle_home + Path.explode("AFP"))

    lazy val remote_isabelle: Other_Isabelle =
      Other_Isabelle(remote_isabelle_home, isabelle_identifier = remote_identifier, ssh = ssh)

    def sync(): Other_Isabelle = {
      Sync.sync(options, Rsync.Context(ssh = ssh), remote_isabelle_home,
        afp_root = build_context.afp_root,
        purge_heaps = true,
        preserve_jars = true)
      remote_isabelle
    }

    def init(): Unit = remote_isabelle.init()

    def benchmark(): Unit = {
      val script =
        Benchmark.benchmark_command(host, ssh = ssh, isabelle_home = remote_isabelle_home)
      remote_isabelle.bash(script).check
    }

    def start(): Process_Result = {
      val remote_ml_platform = remote_isabelle.getenv("ML_PLATFORM")
      if (remote_ml_platform != build_context.ml_platform) {
        error("Bad ML_PLATFORM: found " + remote_ml_platform +
          ", but expected " + build_context.ml_platform)
      }
      val script =
        Build.build_worker_command(host,
          ssh = ssh,
          build_options = List(options.spec("build_database_server")),
          build_id = build_context.build_uuid,
          isabelle_home = remote_isabelle_home,
          afp_root = remote_afp_root,
          dirs = Path.split(host.dirs).map(remote_isabelle.expand_path),
          quiet = true)
      remote_isabelle.bash(script).check
    }

    override def close(): Unit = ssh.close()
  }

  class Result(val host: Host, val process_result: Exn.Result[Process_Result]) {
    def rc: Int = Process_Result.RC(process_result)
    def ok: Boolean = rc == Process_Result.RC.ok
  }


  /* build clusters */

  object none extends Build_Cluster {
    override def toString: String = "Build_Cluster.none"
  }

  def make(build_context: Build.Context, progress: Progress = new Progress): Build_Cluster = {
    val remote_hosts = build_context.build_hosts.filterNot(_.is_local)
    if (remote_hosts.isEmpty) none
    else new Remote_Build_Cluster(build_context, remote_hosts, progress = progress)
  }
}

// NB: extensible via Build.Engine.build_process() and Build_Process.init_cluster()
trait Build_Cluster extends AutoCloseable {
  def rc: Int = Process_Result.RC.ok
  def ok: Boolean = rc == Process_Result.RC.ok
  def return_code(rc: Int): Unit = ()
  def return_code(res: Process_Result): Unit = return_code(res.rc)
  def return_code(exn: Throwable): Unit = return_code(Process_Result.RC(exn))
  def open(): Unit = ()
  def init(): Unit = ()
  def benchmark(): Unit = ()
  def start(): Unit = ()
  def active(): Boolean = false
  def join: List[Build_Cluster.Result] = Nil
  def stop(): Unit = { join; close() }
  override def close(): Unit = ()
}

class Remote_Build_Cluster(
  val build_context: Build.Context,
  val remote_hosts: List[Build_Cluster.Host],
  val progress: Progress = new Progress
) extends Build_Cluster {
  require(remote_hosts.nonEmpty && !remote_hosts.exists(_.is_local), "remote hosts required")

  override def toString: String =
    remote_hosts.iterator.map(_.name).mkString("Build_Cluster(", ", ", ")")


  /* cumulative return code */

  private val _rc = Synchronized(Process_Result.RC.ok)

  override def rc: Int = _rc.value

  override def return_code(rc: Int): Unit =
    _rc.change(rc0 => Process_Result.RC.merge(rc0, rc))

  def capture[A](host: Build_Cluster.Host, op: String)(
    e: => A,
    msg: String = host.message(op + " ..."),
    err: Throwable => String = { exn =>
      return_code(exn)
      host.message("failed to " + op + "\n" + Exn.print(exn))
    }
  ): Exn.Result[A] = {
    progress.capture(e, msg = msg, err = err)
  }


  /* open remote sessions */

  private var _sessions = List.empty[Build_Cluster.Session]

  override def open(): Unit = synchronized {
    require(_sessions.isEmpty, "build cluster already open")

    val attempts =
      Par_List.map((host: Build_Cluster.Host) =>
        capture(host, "open") { host.open_session(build_context, progress = progress) },
        remote_hosts, thread = true)

    if (attempts.forall(Exn.is_res)) {
      _sessions = attempts.map(Exn.the_res)
      _sessions
    }
    else {
      for (case Exn.Res(session) <- attempts) session.close()
      error("Failed to connect build cluster")
    }
  }


  /* init and benchmark remote Isabelle distributions */

  private var _init = List.empty[Future[Unit]]

  override def init(): Unit = synchronized {
    require(_sessions.nonEmpty, "build cluster not yet open")

    if (_init.isEmpty) {
      _init =
        for (session <- _sessions if !session.host.shared) yield {
          Future.thread(session.host.message("session")) {
            capture(session.host, "sync") { session.sync() }
            capture(session.host, "init") { session.init() }
          }
        }
    }
  }
  
  override def benchmark(): Unit = synchronized {
    _init.foreach(_.join)
    _init =
      for (session <- _sessions if !session.host.shared) yield {
        Future.thread(session.host.message("session")) {
          capture(session.host, "benchmark") { session.benchmark() }
        }
      }
    _init.foreach(_.join)
  }


  /* workers */

  private var _workers = List.empty[Future[Process_Result]]

  override def active(): Boolean = synchronized { _workers.nonEmpty }

  override def start(): Unit = synchronized {
    require(_sessions.nonEmpty, "build cluster not yet open")
    require(_workers.isEmpty, "build cluster already active")

    init()
    _init.foreach(_.join)

    _workers =
      for (session <- _sessions) yield {
        Future.thread(session.host.message("work")) {
          Exn.release(capture(session.host, "work") { session.start() })
        }
      }
  }

  override def join: List[Build_Cluster.Result] = synchronized {
    _init.foreach(_.join)
    if (_workers.isEmpty) Nil
    else {
      assert(_sessions.length == _workers.length)
      for ((session, worker) <- _sessions zip _workers)
        yield Build_Cluster.Result(session.host, worker.join_result)
    }
  }


  /* close */

  override def close(): Unit = synchronized {
    _init.foreach(_.join)
    _workers.foreach(_.join_result)
    _sessions.foreach(_.close())

    _init = Nil
    _workers = Nil
    _sessions = Nil
  }
}
