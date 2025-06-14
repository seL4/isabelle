/*  Title:      Pure/Build/build_cluster.scala
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
    private val HOME = "home"
    private val SHARED = "shared"

    val parameters: Options =
      Options.inline("""
        option hostname : string = "" -- "explicit SSH hostname"
        option user : string = ""     -- "explicit SSH user"
        option port : int = 0         -- "explicit SSH port"
        option jobs : int = 1         -- "maximum number of parallel jobs"
        option numa : bool = false    -- "cyclic shuffling of NUMA CPU nodes"
        option dirs : string = ""     -- "additional session directories (separated by colon)"
        option home : string = ""     -- "alternative user home (via $USER_HOME)"
        option shared : bool = false  -- "shared home directory: omit sync + init"
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
      home: String = parameters.string(HOME),
      shared: Boolean = parameters.bool(SHARED),
      options: List[Options.Spec] = Nil
    ): Host = {
      new Host(name, hostname, user, port, jobs, numa, dirs, home, shared, options)
    }

    def parse(registry: Registry, str: String): List[Host] = {
      def err(msg: String): Nothing =
        cat_error(msg, "The error(s) above occurred in host specification " + quote(str))

      val names = str.takeWhile(c => !rfc822_specials.contains(c) || c == ',')
      val more_specs =
        try {
          val n = str.length
          val m = names.length
          val l =
            if (m == n) n
            else if (str(m) == ':') m + 1
            else error("Missing \":\" after host name")
          Options.Spec.parse(str.substring(l))
        }
        catch { case ERROR(msg) => err(msg) }

      def get_registry(a: String): Registry.Cluster.Value =
        Registry.Cluster.try_unqualify(a) match {
          case Some(b) => Registry.Cluster.get(registry, b)
          case None => List(a -> Registry.Host.get(registry, a))
        }

      for (name <- space_explode(',', names); (host, host_specs) <- get_registry(name))
      yield {
        val (params, options) =
          try {
            val (specs1, specs2) = (host_specs ::: more_specs).partition(is_parameter)
            (parameters ++ specs1, { test_options ++ specs2; specs2 })
          }
          catch { case ERROR(msg) => err(msg) }

        apply(name = host,
          hostname = params.string(HOSTNAME),
          user = params.string(USER),
          port = params.int(PORT),
          jobs = params.int(JOBS),
          numa = params.bool(NUMA),
          dirs = params.string(DIRS),
          home = params.string(HOME),
          shared = params.bool(SHARED),
          options = options)
      }
    }

    def parse_single(registry: Registry, str: String): Host =
      Library.the_single(parse(registry, str), message = "Single host expected: " + quote(str))
  }

  class Host(
    val name: String,
    val hostname: String,
    val user: String,
    val port: Int,
    val jobs: Int,
    val numa: Boolean,
    val dirs: String,
    val home: String,
    val shared: Boolean,
    val options: List[Options.Spec]
  ) {
    host =>

    Path.split(host.dirs)  // check

    def ssh_host: String = proper_string(host.hostname) getOrElse host.name
    def is_local: Boolean = SSH.is_local(ssh_host)
    def is_remote: Boolean = !is_local

    override def toString: String = print

    def print: String = {
      val params =
        List(
          if (host.hostname.isEmpty) "" else Options.Spec.print(Host.HOSTNAME, host.hostname),
          if (host.user.isEmpty) "" else Options.Spec.print(Host.USER, host.user),
          if (host.port == 0) "" else Options.Spec.print(Host.PORT, host.port.toString),
          if (host.jobs == 1) "" else Options.Spec.print(Host.JOBS, host.jobs.toString),
          if_proper(host.numa, Host.NUMA),
          if_proper(host.dirs, Options.Spec.print(Host.DIRS, host.dirs)),
          if_proper(host.home, Options.Spec.print(Host.HOME, host.home)),
          if_proper(host.shared, Host.SHARED)
        ).filter(_.nonEmpty)
      val rest = (params ::: host.options.map(_.print)).mkString(",")

      SSH.print_local(host.name) + if_proper(rest, ":" + rest)
    }

    def message(msg: String): String = "Host " + quote(host.name) + if_proper(msg, ": " + msg)

    def open_ssh(options: Options): SSH.System =
      SSH.open_system(options ++ host.options, ssh_host, port = host.port,
        user = host.user, user_home = host.home)

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

    val build_cluster_identifier: String = options.string("build_cluster_identifier")
    val build_cluster_isabelle_home: Path =
      Path.explode(options.string("build_cluster_root")) + Path.explode("isabelle")

    lazy val build_cluster_isabelle: Other_Isabelle =
      Other_Isabelle(build_cluster_isabelle_home,
        isabelle_identifier = build_cluster_identifier, ssh = ssh)

    def sync(): Other_Isabelle = {
      val context = Rsync.Context(ssh = ssh)
      val target = build_cluster_isabelle_home
      if (Mercurial.Hg_Sync.ok(Path.ISABELLE_HOME)) {
        val source = File.standard_path(Path.ISABELLE_HOME)
        Rsync.exec(context, clean = true,
          args = List("--", Url.direct_path(source), context.target(target))).check
      }
      else {
        Sync.sync(options, context, target,
          purge_heaps = true,
          preserve_jars = true,
          dirs = Sync.afp_dirs(build_context.afp_root))
      }
      build_cluster_isabelle
    }

    def init(): Unit =
      build_cluster_isabelle.init(other_settings =
        build_cluster_isabelle.init_components() ::: build_cluster_isabelle.debug_settings())

    def benchmark(): Unit = {
      val script =
        Build_Benchmark.benchmark_command(options, host, ssh = ssh,
          isabelle_home = build_cluster_isabelle_home)
      build_cluster_isabelle.bash(script).check
    }

    def start(): Process_Result = {
      val build_cluster_ml_platform = build_cluster_isabelle.ml_platform
      if (build_cluster_ml_platform != build_context.ml_platform) {
        error("Bad ML_PLATFORM: found " + build_cluster_ml_platform +
          ", but expected " + build_context.ml_platform)
      }
      val build_options =
        for { option <- options.iterator if option.for_build_sync } yield options.spec(option.name)
      val script =
        Build.build_worker_command(host,
          ssh = ssh,
          build_options = build_options.toList,
          build_id = build_context.build_uuid,
          isabelle_home = build_cluster_isabelle_home,
          dirs = Path.split(host.dirs).map(build_cluster_isabelle.expand_path),
          quiet = true)
      build_cluster_isabelle.bash(script).check
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
    val remote_hosts = build_context.build_hosts.filter(_.is_remote)
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
  def open(): Build_Cluster = this
  def init(): Build_Cluster = this
  def benchmark(): Build_Cluster = this
  def start(): Build_Cluster = this
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
  require(remote_hosts.nonEmpty && remote_hosts.forall(_.is_remote), "remote hosts required")

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

  override def open(): Build_Cluster = synchronized {
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

    this
  }


  /* init and benchmark remote Isabelle distributions */

  private var _init = List.empty[Future[Unit]]

  override def init(): Build_Cluster = synchronized {
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

    this
  }

  override def benchmark(): Build_Cluster = synchronized {
    _init.foreach(_.join)
    _init =
      for (session <- _sessions if !session.host.shared) yield {
        Future.thread(session.host.message("session")) {
          capture(session.host, "benchmark") { session.benchmark() }
        }
      }
    _init.foreach(_.join)

    this
  }


  /* workers */

  private var _workers = List.empty[Future[Process_Result]]

  override def active(): Boolean = synchronized { _workers.nonEmpty }

  override def start(): Build_Cluster = synchronized {
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

    this
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
