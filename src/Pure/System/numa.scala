/*  Title:      Pure/System/numa.scala
    Author:     Makarius

Support for Non-Uniform Memory Access of separate CPU nodes.
*/

package isabelle


object NUMA
{
  /* available nodes */

  def nodes(): List[Int] =
  {
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
      Library.space_explode(',', Library.trim_line(File.read(numa_nodes_linux))).flatMap(read(_))
    }
    else Nil
  }


  /* CPU policy via numactl tool */

  lazy val numactl_available: Boolean = Isabelle_System.bash("numactl --hardware").ok

  def policy(node: Int): String =
    if (numactl_available) "numactl -m" + node + " -N" + node else ""
}
