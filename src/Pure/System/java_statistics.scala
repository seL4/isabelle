/*  Title:      Pure/System/java_statistics.scala
    Author:     Makarius

Java runtime statistics.
*/

package isabelle

import java.lang.management.{ManagementFactory, MemoryUsage}
import com.sun.management.GarbageCollectorMXBean

import scala.jdk.CollectionConverters._


object Java_Statistics {
  /* GC status */

  sealed case class GC_Status(
    name: String,
    count: Long,
    duration: Time,
    size_before_gc: Space,
    used_before_gc: Space,
    size_after_gc: Space,
    used_after_gc: Space
  ) {
    def free_before_gc: Space = size_before_gc - used_before_gc
    def free_after_gc: Space = size_after_gc - used_after_gc
    def is_proper: Boolean =
      size_before_gc.is_proper || used_before_gc.is_proper ||
      size_after_gc.is_proper || used_after_gc.is_proper
  }

  def gc_status(): List[GC_Status] =
    List.from(
      for {
        gc_bean <- ManagementFactory.getPlatformMXBeans(classOf[GarbageCollectorMXBean]).asScala.iterator
        if gc_bean.isValid
        gc_info <- Option(gc_bean.getLastGcInfo)
      } yield {
        def sum(usage: java.util.Map[String, MemoryUsage], which: MemoryUsage => Long): Space =
          Space.bytes(usage.asScala.valuesIterator.map(which).sum)

        val before_gc = gc_info.getMemoryUsageBeforeGc
        val after_gc = gc_info.getMemoryUsageAfterGc
        GC_Status(
          name = gc_bean.getName,
          count = gc_bean.getCollectionCount,
          duration = Time.ms(gc_info.getDuration),
          size_before_gc = sum(before_gc, _.getCommitted),
          used_before_gc = sum(before_gc, _.getUsed),
          size_after_gc = sum(after_gc, _.getCommitted),
          used_after_gc = sum(after_gc, _.getUsed)
        )
      }
    )


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
    val gc = gc_status()
    val memory = memory_status()
    val threads = Thread.activeCount()
    val workers = Isabelle_Thread.pool.getPoolSize
    val workers_active = Isabelle_Thread.pool.getActiveCount

    val res1 =
      gc.find(_.is_proper) match {
        case None => Nil
        case Some(heap) =>
          List(
            "java_heap_size_before_gc" -> heap.size_before_gc.toString,
            "java_heap_used_before_gc" -> heap.used_before_gc.toString,
            "java_heap_size_after_gc" -> heap.size_after_gc.toString,
            "java_heap_used_after_gc" -> heap.used_after_gc.toString)
      }
    val res2 =
      List(
        "java_heap_size" -> memory.heap_size.toString,
        "java_heap_used" -> memory.heap_used.toString,
        "java_threads_total" -> threads.toString,
        "java_workers_total" -> workers.toString,
        "java_workers_active" -> workers_active.toString)

    res1 ::: res2
  }
}
