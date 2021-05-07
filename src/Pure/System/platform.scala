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
  val is_unix: Boolean = is_linux || is_macos

  def is_arm: Boolean = cpu_arch.startsWith("arm")

  def family: Family.Value =
    if (is_linux && is_arm) Family.linux_arm
    else if (is_linux) Family.linux
    else if (is_macos) Family.macos
    else if (is_windows) Family.windows
    else error("Failed to determine current platform family")

  object Family extends Enumeration
  {
    val linux_arm, linux, macos, windows = Value
    val list0: List[Value] = List(linux, windows, macos)
    val list: List[Value] = List(linux_arm, linux, windows, macos)

    def unapply(name: String): Option[Value] =
      try { Some(withName(name)) }
      catch { case _: NoSuchElementException => None }

    def parse(name: String): Value =
      unapply(name) getOrElse error("Bad platform family: " + quote(name))

    def standard(platform: Value): String =
      if (platform == linux_arm) "arm64-linux"
      else if (platform == linux) "x86_64-linux"
      else if (platform == macos) "x86_64-darwin"
      else if (platform == windows) "x86_64-cygwin"
      else error("Bad platform family: " + quote(platform.toString))
  }


  /* platform identifiers */

  private val X86 = """i.86|x86""".r
  private val X86_64 = """amd64|x86_64""".r
  private val Arm64 = """arm64|aarch64""".r
  private val Arm32 = """arm""".r

  def cpu_arch: String =
    System.getProperty("os.arch", "") match {
      case X86() => "x86"
      case X86_64() => "x86_64"
      case Arm64() => "arm64"
      case Arm32() => "arm32"
      case _ => error("Failed to determine CPU architecture")
    }

  def os_name: String =
    family match {
      case Family.linux_arm => "linux"
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
}
