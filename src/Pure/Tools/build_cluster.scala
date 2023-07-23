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

    private val USER = "user"
    private val PORT = "port"
    private val JOBS = "jobs"
    private val NUMA = "numa"

    val parameters: Options =
      Options.inline("""
        option user : string = ""   -- "explicit SSH user"
        option port : int = 0       -- "explicit SSH port"
        option jobs : int = 1       -- "maximum number of parallel jobs"
        option numa : bool = false  -- "cyclic shuffling of NUMA CPU nodes"
      """)

    def is_parameter(spec: Options.Spec): Boolean = parameters.defined(spec.name)

    lazy val test_options: Options = Options.init0()

    def apply(
      name: String = "",
      user: String = parameters.string(USER),
      port: Int = parameters.int(PORT),
      jobs: Int = parameters.int(JOBS),
      numa: Boolean = parameters.bool(NUMA),
      options: List[Options.Spec] = Nil
    ): Host = new Host(name, user, port, jobs, numa, options)

    def parse(str: String): Host = {
      val name = str.takeWhile(c => !rfc822_specials.contains(c))
      val (params, options) =
        try {
          val rest = {
            val n = str.length
            val m = name.length
            val l =
              if (m == n) n
              else if (str(m) == ':') m + 1
              else error("Missing \":\" after host name")
            str.substring(l)
          }
          val (specs1, specs2) = Options.parse_specs(rest).partition(is_parameter)
          (parameters ++ specs1, { test_options ++ specs2; specs2 })
        }
        catch {
          case ERROR(msg) =>
            cat_error(msg, "The error(s) above occurred in host specification " + quote(str))
        }
      apply(name = name,
        user = params.string(USER),
        port = params.int(PORT),
        jobs = params.int(JOBS),
        numa = params.bool(NUMA),
        options = options)
    }

    def print_name(s: String): String =
      Token.quote_name(Options.specs_syntax.keywords, s)

    def print_option(spec: Options.Spec): String = {
      def print_value =
        spec.value.get match {
          case s@Value.Boolean(_) => s
          case s@Value.Long(_) => s
          case s@Value.Double(_) => s
          case s => print_name(s)
        }
      spec.name + if_proper(spec.value, "=" + print_value)
    }
  }

  class Host(
    val name: String,
    val user: String,
    val port: Int,
    val jobs: Int,
    val numa: Boolean,
    val options: List[Options.Spec]
  ) {
    host =>

    def is_local: Boolean = SSH.is_local(host.name)

    override def toString: String = print

    def print: String = {
      val params =
        List(
          if (host.user.isEmpty) "" else Properties.Eq(Host.USER, Host.print_name(host.user)),
          if (host.port == 0) "" else Properties.Eq(Host.PORT, host.port.toString),
          if (host.jobs == 1) "" else Properties.Eq(Host.JOBS, host.jobs.toString),
          if_proper(host.numa, Host.NUMA)
        ).filter(_.nonEmpty)
      val rest = (params ::: host.options.map(Host.print_option)).mkString(",")

      SSH.print_local(host.name) + if_proper(rest, ":" + rest)
    }

    def message(msg: String): String = "Host " + quote(host.name) + if_proper(msg, ": " + msg)
    def err_message(msg: String)(exn: Throwable): String = message(msg + "\n" + Exn.message(exn))

    def open_session(
      options: Options,
      afp_root: Option[Path] = None,
      progress: Progress = new Progress
    ): Session = {
      val session_options = options ++ host.options
      val ssh = SSH.open_session(session_options, host.name, port = host.port, user = host.user)
      new Session(host, session_options, afp_root, ssh, progress)
    }
  }


  /* SSH sessions */

  class Session(
    val host: Host,
    val options: Options,
    val afp_root: Option[Path],
    val ssh: SSH.System,
    val progress: Progress
  ) extends AutoCloseable {
    override def toString: String = ssh.toString

    val remote_identifier: String = options.string("build_cluster_identifier")
    val remote_root: Path = Path.explode(options.string("build_cluster_root"))
    val remote_isabelle_home: Path = remote_root + Path.explode("isabelle")
    val remote_afp: Path = remote_isabelle_home + Path.explode("AFP")

    def remote_isabelle: Other_Isabelle =
      Other_Isabelle(remote_isabelle_home, isabelle_identifier = remote_identifier, ssh = ssh)

    def init(): Unit = {
      Exn.release(
        progress.capture(
          Sync.sync(options, Rsync.Context(ssh = ssh), remote_isabelle_home,
            afp_root = afp_root, purge_heaps = true, preserve_jars = true),
          msg = host.message("sync ..."),
          err = host.err_message("failed to sync")))

      Exn.release(
        progress.capture(remote_isabelle.init(),
          msg = host.message("init ..."),
          err = host.err_message("failed to init")))
    }

    def start(): Process_Result = {
      Process_Result.ok  // FIXME
    }

    override def close(): Unit = ssh.close()
  }

  class Result(val host: Host, val process_result: Exn.Result[Process_Result]) {
    def ok: Boolean =
      process_result match {
        case Exn.Res(res) => res.ok
        case Exn.Exn(_) => false
      }
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
  def open(): Unit = ()
  def init(): Unit = ()
  def start(): Unit = ()
  def active(): Boolean = false
  def join: List[Build_Cluster.Result] = Nil
  def stop(): Unit = { join; close() }
  def rc: Int = Process_Result.RC.ok
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


  /* remote sessions */

  private var _sessions = List.empty[Build_Cluster.Session]

  override def open(): Unit = synchronized {
    require(_sessions.isEmpty, "build cluster already open")

    val attempts =
      Par_List.map((host: Build_Cluster.Host) =>
        progress.capture(
          host.open_session(build_context.build_options, progress = progress),
          msg = host.message("open ..."),
          err = host.err_message("failed to open")),
        remote_hosts, thread = true)

    if (attempts.forall(Exn.the_res.isDefinedAt)) {
      _sessions = attempts.map(Exn.the_res)
      _sessions
    }
    else {
      for (Exn.Res(session) <- attempts) session.close()
      error("Failed to connect build cluster")
    }
  }


  /* init */

  private var _init = List.empty[Future[Unit]]

  override def init(): Unit = synchronized {
    require(_sessions.nonEmpty, "build cluster not yet open")

    if (_init.isEmpty) {
      _init = _sessions.map(session =>
        Future.thread(session.host.message("init")) { session.init() })
    }
  }


  /* workers */

  private var _workers = List.empty[Future[Process_Result]]

  override def active(): Boolean = synchronized { _workers.nonEmpty }

  override def start(): Unit = synchronized {
    require(_sessions.nonEmpty, "build cluster not yet open")
    require(_workers.isEmpty, "build cluster already active")

    init()
    _init.foreach(_.join)

    _workers = _sessions.map(session =>
      Future.thread(session.host.message("start")) { session.start() })
  }

  override def join: List[Build_Cluster.Result] = synchronized {
    if (_workers.isEmpty) Nil
    else {
      assert(_sessions.length == _workers.length)
      for ((session, worker) <- _sessions zip _workers)
        yield Build_Cluster.Result(session.host, worker.join_result)
    }
  }


  /* close */

  private var _rc: Int = Process_Result.RC.ok

  override def rc: Int = synchronized { _rc }

  override def close(): Unit = synchronized {
    _init.foreach(_.cancel())
    _workers.foreach(_.cancel())
    join
    _sessions.foreach(_.close())

    val rc1 = Process_Result.RC(_init.iterator.map(_.join_result).forall(Exn.the_res.isDefinedAt))
    val rcs2 = _workers.map(worker => Process_Result.RC(worker.join_result))
    _rc = Process_Result.RC.merge(rc1 :: rcs2)

    _workers = Nil
    _sessions = Nil
  }
}
