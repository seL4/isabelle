/*  Title:      Pure/System/numa.scala
    Author:     Makarius

Support for Non-Uniform Memory Access of separate CPU nodes.
*/

package isabelle


object NUMA {
  /* information about nodes */

  private val numa_info_linux: Path = Path.explode("/sys/devices/system/node/online")

  private val Info_Single = """^(\d+)$""".r
  private val Info_Multiple = """^(\d+)-(\d+)$""".r

  private def parse_nodes(s: String): List[Int] =
    s match {
      case Info_Single(Value.Int(i)) => List(i)
      case Info_Multiple(Value.Int(i), Value.Int(j)) => (i to j).toList
      case _ => error("Cannot parse CPU node specification: " + quote(s))
    }

  def nodes(enabled: Boolean = true, ssh: SSH.System = SSH.Local): List[Int] = {
    val numa_info = if (ssh.isabelle_platform.is_linux) Some(numa_info_linux) else None
    for {
      path <- numa_info.toList
      if enabled && ssh.is_file(path)
      s <- space_explode(',', ssh.read(path).trim)
      n <- parse_nodes(s)
    } yield n
  }


  /* CPU policy via numactl tool */

  def numactl(node: Int): String = "numactl -m" + node + " -N" + node
  def numactl_ok(node: Int): Boolean = Isabelle_System.bash(numactl(node) + " true").ok

  def policy(node: Int): String = if (numactl_ok(node)) numactl(node) else ""

  def policy_options(options: Options, numa_node: Option[Int]): Options =
    numa_node match {
      case None => options
      case Some(n) => options.string("ML_process_policy") = policy(n)
    }

  def perhaps_policy_options(options: Options): Options = {
    val numa_node =
      try {
        nodes() match {
          case ns if ns.length >= 2 && numactl_ok(ns.head) => Some(ns.head)
          case _ => None
        }
      }
      catch { case ERROR(_) => None }
    policy_options(options, numa_node)
  }


  /* shuffling of CPU nodes */

  def check(progress: Progress, enabled: Boolean): Boolean = {
    def warning =
      nodes() match {
        case ns if ns.length < 2 => Some("no NUMA nodes available")
        case ns if !numactl_ok(ns.head) => Some("bad numactl tool")
        case _ => None
      }

    enabled &&
      (warning match {
        case Some(s) => progress.echo_warning("Shuffling of CPU nodes is disabled: " + s); false
        case _ => true
      })
  }
}
