/*  Title:      Pure/System/java_statistics.scala
    Author:     Makarius

Java runtime statistics.
*/

package isabelle


object Java_Statistics {
  /* memory status */

  sealed case class Memory_Status(heap_size: Space, heap_free: Space) {
    def heap_used: Space = heap_size.used(heap_free)
    def heap_used_fraction: Double = heap_size.used_fraction(heap_free)
  }

  def memory_status(): Memory_Status = {
    val heap_size = Space.bytes(Runtime.getRuntime.totalMemory())
    val heap_free = Space.bytes(Runtime.getRuntime.freeMemory())
    Memory_Status(heap_size, heap_free)
  }


  /* JVM statistics */

  def jvm_statistics(): Properties.T = {
    val status = memory_status()
    val threads = Thread.activeCount()
    val workers = Isabelle_Thread.pool.getPoolSize
    val workers_active = Isabelle_Thread.pool.getActiveCount

    List(
      "java_heap_size" -> status.heap_size.toString,
      "java_heap_used" -> status.heap_used.toString,
      "java_threads_total" -> threads.toString,
      "java_workers_total" -> workers.toString,
      "java_workers_active" -> workers_active.toString)
  }
}
