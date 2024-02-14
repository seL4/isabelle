/*  Title:      Pure/Concurrent/multithreading.scala
    Author:     Makarius

Multithreading in Isabelle/Scala.
*/

package isabelle


object Multithreading {
  /* physical processors */

  def num_processors(ssh: SSH.System = SSH.Local): Int =
    if (ssh.isabelle_platform.is_macos) {
      val result = ssh.execute("sysctl -n hw.physicalcpu").check
      Library.trim_line(result.out) match {
        case Value.Int(n) => n
        case _ => 1
      }
    }
    else {
      val Core_Id = """^\s*core id\s*:\s*(\d+)\s*$""".r
      val cpuinfo = ssh.read(Path.explode("/proc/cpuinfo"))
      (for (case Core_Id(Value.Int(i)) <- Library.trim_split_lines(cpuinfo)) yield i).toSet.size
    }


  /* max_threads */

  def max_threads(): Int = {
    val m = Value.Int.unapply(System.getProperty("isabelle.threads", "0")) getOrElse 0
    if (m > 0) m else (num_processors() max 1) min 8
  }
}
