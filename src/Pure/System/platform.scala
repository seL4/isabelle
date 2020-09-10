/*  Title:      Pure/System/platform.scala
    Author:     Makarius

System platform identification.
*/

package isabelle


object Platform
{
  /* platform family */

  val is_linux: Boolean = System.getProperty("os.name", "") == "Linux"
  val is_macos: Boolean = System.getProperty("os.name", "") == "Mac OS X"
  val is_windows: Boolean = System.getProperty("os.name", "").startsWith("Windows")

  def family: Family.Value =
    if (is_linux) Family.linux
    else if (is_macos) Family.macos
    else if (is_windows) Family.windows
    else error("Failed to determine current platform family")

  object Family extends Enumeration
  {
    val linux, macos, windows = Value

    def unapply(name: String): Option[Value] =
      try { Some(withName(name)) }
      catch { case _: NoSuchElementException => None }

    def parse(name: String): Value =
      unapply(name) getOrElse error("Bad platform family: " + quote(name))
  }


  /* platform identifiers */

  private val X86 = """i.86|x86""".r
  private val X86_64 = """amd64|x86_64""".r

  def cpu_arch: String =
    System.getProperty("os.arch", "") match {
      case X86() => "x86"
      case X86_64() => "x86_64"
      case _ => error("Failed to determine CPU architecture")
    }

  def os_name: String =
    family match {
      case Family.macos => "darwin"
      case _ => family.toString
    }

  lazy val jvm_platform: String = cpu_arch + "-" + os_name


  /* JVM version */

  private val Version = """1\.(\d+)\.0_(\d+)""".r
  lazy val jvm_version: String =
    System.getProperty("java.version") match {
      case Version(a, b) => a + "u" + b
      case a => a
    }


  /* JVM name */

  val jvm_name: String = System.getProperty("java.vm.name", "")


  /* memory status */

  sealed case class Memory_Status(heap_size: Long, heap_free: Long)
  {
    def heap_used: Long = (heap_size - heap_free) max 0
    def heap_used_fraction: Double =
      if (heap_size == 0) 0.0 else heap_used.toDouble / heap_size
  }

  def memory_status(): Memory_Status =
  {
    val heap_size = Runtime.getRuntime.totalMemory()
    val heap_used = heap_size - Runtime.getRuntime.freeMemory()
    Memory_Status(heap_size, heap_used)
  }


  /* JVM statistics */

  def jvm_statistics(): Properties.T =
  {
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
