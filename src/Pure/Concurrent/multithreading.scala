/*  Title:      Pure/Concurrent/multithreading.scala
    Author:     Makarius

Multithreading in Isabelle/Scala.
*/

package isabelle


object Multithreading {
  /* physical processors */

  // slightly different from Poly/ML (more accurate)
  def num_processors(ssh: SSH.System = SSH.Local): Int =
    if (ssh.isabelle_platform.is_macos) {
      val result = ssh.execute("sysctl -n hw.physicalcpu").check
      Library.trim_line(result.out) match {
        case Value.Int(n) => n
        case _ => 1
      }
    }
    else {
      val Physical = """^\s*physical id\s*:\s*(\d+)\s*$""".r
      val Cores = """^\s*cpu cores\s*:\s*(\d+)\s*$""".r

      var physical: Option[Int] = None
      var physical_cores = Map.empty[Int, Int]

      val cpuinfo = ssh.read(Path.explode("/proc/cpuinfo"))
      for (line <- Library.trim_split_lines(cpuinfo)) {
        line match {
          case Physical(Value.Int(i)) => physical = Some(i)
          case Cores(Value.Int(i))
            if physical.isDefined && !physical_cores.isDefinedAt(physical.get) =>
            physical_cores = physical_cores + (physical.get -> i)
          case _ =>
        }
      }
      physical_cores.valuesIterator.sum
    }


  /* max_threads */

  def max_threads(): Int = {
    val m = Value.Int.unapply(System.getProperty("isabelle.threads", "0")) getOrElse 0
    if (m > 0) m else (num_processors() max 1) min 8
  }
}
