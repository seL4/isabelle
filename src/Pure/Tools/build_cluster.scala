/*  Title:      Pure/Tools/build_cluster.scala
    Author:     Makarius

Management of build cluster: independent ssh hosts with access to shared
PostgreSQL server.
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

  final class Host private(
    val name: String,
    val user: String,
    val port: Int,
    val jobs: Int,
    val numa: Boolean,
    val options: List[Options.Spec]
  ) {
    def is_local: Boolean = SSH.is_local(name)

    override def toString: String = print

    def print: String = {
      val params =
        List(
          if (user.isEmpty) "" else Properties.Eq(Host.USER, Host.print_name(user)),
          if (port == 0) "" else Properties.Eq(Host.PORT, port.toString),
          if (jobs == 1) "" else Properties.Eq(Host.JOBS, jobs.toString),
          if_proper(numa, Host.NUMA)
        ).filter(_.nonEmpty)
      val rest = (params ::: options.map(Host.print_option)).mkString(",")

      SSH.print_local(name) + if_proper(rest, ":" + rest)
    }

    def message(msg: String): String = "Host " + quote(name) + if_proper(msg, ": " + msg)
  }


  /* remote sessions */

  object Session {
    def open(options: Options, host: Host, progress: Progress = new Progress): Session = {
      val ssh_options = options ++ host.options
      val ssh = SSH.open_session(ssh_options, host.name, port = host.port, user = host.user)
      new Session(host, ssh, progress)
    }
  }

  final class Session private(
    val host: Host,
    val ssh: SSH.Session,
    val progress: Progress
  ) extends AutoCloseable {
    override def toString: String = ssh.toString

    def options: Options = ssh.options

    def start(): Process_Result = {
      Process_Result.ok  // FIXME
    }

    override def close(): Unit = ssh.close()
  }

  sealed case class Result(host: Host, process_result: Exn.Result[Process_Result]) {
    def ok: Boolean =
      process_result match {
        case Exn.Res(res) => res.ok
        case Exn.Exn(_) => false
      }
  }


  /* build clusters */

  val none: Build_Cluster = new No_Build_Cluster

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
  override def close(): Unit = ()
}

final class No_Build_Cluster extends Build_Cluster {
  override def toString: String = "Build_Cluster.none"
}

class Remote_Build_Cluster(
  build_context: Build.Context,
  remote_hosts: List[Build_Cluster.Host],
  progress: Progress = new Progress
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
          Build_Cluster.Session.open(build_context.build_options, host, progress = progress),
          msg = host.message("open ..."),
          err = exn => host.message("failed to open\n" + Exn.message(exn))),
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


  /* workers */

  private var _workers = List.empty[Future[Process_Result]]

  override def active(): Boolean = synchronized { _workers.nonEmpty }

  override def start(): Unit = synchronized {
    require(_sessions.nonEmpty, "build cluster not yet open")
    require(_workers.isEmpty, "build cluster already active")

    _workers = _sessions.map(session =>
      Future.thread(session.host.message("session")) { session.start() })
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

  override def close(): Unit = synchronized {
    _workers.foreach(_.cancel())
    join
    _sessions.foreach(_.close())
    _workers = Nil
    _sessions = Nil
  }
}
