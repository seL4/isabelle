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
      host: String = "",
      user: String = parameters.string(USER),
      port: Int = parameters.int(PORT),
      jobs: Int = parameters.int(JOBS),
      numa: Boolean = parameters.bool(NUMA),
      options: List[Options.Spec] = Nil
    ): Host = new Host(host, user, port, jobs, numa, options)

    def parse(str: String): Host = {
      val host = str.takeWhile(c => !rfc822_specials.contains(c))
      val (params, options) =
        try {
          val rest = {
            val n = str.length
            val m = host.length
            val l =
              if (m == n) n
              else if (str(m) == ':') m + 1
              else error("Colon (:) expected after host name")
            str.substring(l)
          }
          val (specs1, specs2) = Options.parse_specs(rest).partition(is_parameter)
          (parameters ++ specs1, { test_options ++ specs2; specs2 })
        }
        catch {
          case ERROR(msg) =>
            cat_error(msg, "The error(s) above occurred in host specification " + quote(str))
        }
      apply(host = host,
        user = params.string(USER),
        port = params.int(PORT),
        jobs = params.int(JOBS),
        numa = params.bool(NUMA),
        options = options)
    }
  }

  final class Host private(
    host: String,
    user: String,
    port: Int,
    jobs: Int,
    numa: Boolean,
    options: List[Options.Spec]
  ) {
    def is_remote: Boolean = host.nonEmpty

    override def toString: String = print

    def print: String = {
      val params =
        List(
          if (user.isEmpty) "" else Properties.Eq(Host.USER, user),
          if (port == 0) "" else Properties.Eq(Host.PORT, port.toString),
          if (jobs == 1) "" else Properties.Eq(Host.JOBS, jobs.toString),
          if_proper(numa, Host.NUMA)
        ).filter(_.nonEmpty)
      val rest = (params ::: options).mkString(",")

      if (host.isEmpty) ":" + rest
      else if (rest.isEmpty) host
      else host + ":" + rest
    }

    def open_ssh_session(options: Options): SSH.Session =
      SSH.open_session(options, host, port = port, user = user)
  }


  /* remote sessions */

  class Session(host: Host) extends AutoCloseable {
    override def close(): Unit = ()
  }
}

// class extensible via Build.Engine.build_process() and Build_Process.init_cluster()
class Build_Cluster(
  build_context: Build_Process.Context,
  remote_hosts: List[Build_Cluster.Host],
  progress: Progress = new Progress
) extends AutoCloseable {
  require(remote_hosts.nonEmpty && remote_hosts.forall(_.is_remote), "remote hosts required")

  override def toString: String = remote_hosts.mkString("Build_Cluster(", ", ", ")")

  progress.echo("Remote hosts:\n" + cat_lines(remote_hosts.map("  " + _)))

  def start(): Unit = ()
  def stop(): Unit = ()

  override def close(): Unit = ()
}
