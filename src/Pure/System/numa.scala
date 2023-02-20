/*  Title:      Pure/System/numa.scala
    Author:     Makarius

Support for Non-Uniform Memory Access of separate CPU nodes.
*/

package isabelle


object NUMA {
  /* available nodes */

  def nodes(): List[Int] = {
    val numa_nodes_linux = Path.explode("/sys/devices/system/node/online")

    val Single = """^(\d+)$""".r
    val Multiple = """^(\d+)-(\d+)$""".r

    def read(s: String): List[Int] =
      s match {
        case Single(Value.Int(i)) => List(i)
        case Multiple(Value.Int(i), Value.Int(j)) => (i to j).toList
        case _ => error("Cannot parse CPU node specification: " + quote(s))
      }

    if (numa_nodes_linux.is_file) {
      space_explode(',', File.read(numa_nodes_linux).trim).flatMap(read)
    }
    else Nil
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

  def enabled_warning(progress: Progress, enabled: Boolean): Boolean = {
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
