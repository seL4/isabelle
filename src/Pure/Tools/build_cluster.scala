/*  Title:      Pure/Tools/build_cluster.scala
    Author:     Makarius

Management of build cluster: independent ssh hosts with access to shared
PostgreSQL server.
*/

package isabelle


object Build_Cluster {
  object Host {
    val PORT = "port"
    val JOBS = "jobs"
    val NUMA = "numa"

    def apply(
      host: String,
      user: String = "",
      port: Int = 0,
      jobs: Int = 1,
      numa: Boolean = false,
      options: List[Options.Spec] = Nil
    ): Host = new Host(host, user, port, jobs, numa, options)

    def parse(str: String): Host = Host(host = str)  // FIXME proper parse
  }

  final class Host private(
    host: String,
    user: String,
    port: Int,
    jobs: Int,
    numa: Boolean,
    options: List[Options.Spec]
  ) {
    require(host.nonEmpty, "Undefined host name")

    override def toString: String = print
    def print: String = {
      val props =
        List(
          if (port == 0) "" else Properties.Eq(Host.PORT, port.toString),
          if (jobs == 1) "" else Properties.Eq(Host.JOBS, jobs.toString),
          if_proper(numa, Host.NUMA)
        ).filter(_.nonEmpty)
      val rest = (props ::: options).mkString(",")
      if_proper(user, user + "@") + host + if_proper(rest, ":" + rest)
    }

    def open_ssh_session(options: Options): SSH.Session =
      SSH.open_session(options, host, port = port, user = user)
  }
}
