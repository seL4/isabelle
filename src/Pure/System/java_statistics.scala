/*  Title:      Pure/System/java_statistics.scala
    Author:     Makarius

Java runtime statistics.
*/

package isabelle

import java.lang.management.{ManagementFactory, MemoryUsage}
import com.sun.management.GarbageCollectorMXBean

import scala.jdk.CollectionConverters._


object Java_Statistics {
  /* GC status (for ZGC) */

  object GC_Status {
    val none: GC_Status = GC_Status()
  }

  sealed case class GC_Status(
    count: Long = 0,
    duration: Time = Time.zero,
    size_before_gc: Space = Space.zero,
    used_before_gc: Space = Space.zero,
    size_after_gc: Space = Space.zero,
    used_after_gc: Space = Space.zero
  ) {
    def free_before_gc: Space = size_before_gc - used_before_gc
    def free_after_gc: Space = size_after_gc - used_after_gc
    def is_proper: Boolean =
      size_before_gc.is_proper || used_before_gc.is_proper ||
      size_after_gc.is_proper || used_after_gc.is_proper
  }

  def gc_status(major: Boolean = false): GC_Status = {
    val gc_beans =
      ManagementFactory.getPlatformMXBeans(classOf[GarbageCollectorMXBean]).asScala
        .find(gc_bean =>
          gc_bean.isValid && gc_bean.getLastGcInfo != null &&
            gc_bean.getName == (if (major) "ZGC Major Cycles" else "ZGC Minor Cycles"))
    gc_beans match {
      case None => GC_Status.none
      case Some(gc_bean) =>
        def sum(usage: java.util.Map[String, MemoryUsage], which: MemoryUsage => Long): Space =
          Space.bytes(usage.asScala.valuesIterator.map(which).sum)

        val gc_info = gc_bean.getLastGcInfo
        val before_gc = gc_info.getMemoryUsageBeforeGc
        val after_gc = gc_info.getMemoryUsageAfterGc
        GC_Status(
          count = gc_bean.getCollectionCount,
          duration = Time.ms(gc_info.getDuration),
          size_before_gc = sum(before_gc, _.getCommitted),
          used_before_gc = sum(before_gc, _.getUsed),
          size_after_gc = sum(after_gc, _.getCommitted),
          used_after_gc = sum(after_gc, _.getUsed))
    }
  }


  /* memory status */

  sealed case class Memory_Status(
    heap_size_minor: Space,
    heap_free_minor: Space,
    heap_size_major: Space,
    heap_free_major: Space
  ) {
    def heap_used_minor: Space = heap_size_minor.used(heap_free_minor)
    def heap_used_minor_fraction: Double = heap_size_minor.used_fraction(heap_free_minor)
    def heap_used_major: Space = heap_size_major.used(heap_free_major)
    def heap_used_major_fraction: Double = heap_size_major.used_fraction(heap_free_major)
  }

  def memory_status(): Memory_Status = {
    val gc_minor = gc_status()
    val gc_major = gc_status(major = true)
    Memory_Status(
      heap_size_minor = gc_minor.size_after_gc,
      heap_free_minor = gc_minor.free_after_gc,
      heap_size_major = gc_major.size_after_gc,
      heap_free_major = gc_major.free_after_gc)
  }


  /* JVM statistics */

  def jvm_statistics(): Properties.T = {
    val memory = memory_status()
    val threads = Thread.activeCount()
    val workers = Isabelle_Thread.pool.getPoolSize
    val workers_active = Isabelle_Thread.pool.getActiveCount
    List(
      ML_Statistics.Java_Heap_Size.name -> memory.heap_size_minor.toString,
      ML_Statistics.Java_Heap_Used.name -> memory.heap_used_minor.toString,
      ML_Statistics.Java_Heap_Size_Major.name -> memory.heap_size_major.toString,
      ML_Statistics.Java_Heap_Used_Major.name -> memory.heap_used_major.toString,
      ML_Statistics.Java_Threads_Total.name -> threads.toString,
      ML_Statistics.Java_Workers_Total.name -> workers.toString,
      ML_Statistics.Java_Workers_Active.name -> workers_active.toString)
  }
}
