/*  Title:      Pure/Concurrent/multithreading.scala
    Author:     Makarius

Multithreading in Isabelle/Scala.
*/

package isabelle


object Multithreading {
  /* max_threads */

  def max_threads(): Int = {
    val m = Value.Int.unapply(System.getProperty("isabelle.threads", "0")) getOrElse 0
    if (m > 0) m else (Host.num_cpus() max 1) min 8
  }
}
