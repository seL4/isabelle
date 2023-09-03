/*  Title:      Pure/System/platform.scala
    Author:     Makarius

System platform identification.
*/

package isabelle


object Platform {
  /* platform family */

  val is_windows: Boolean = isabelle.setup.Environment.is_windows()
  val is_linux: Boolean = System.getProperty("os.name", "") == "Linux"
  val is_macos: Boolean = System.getProperty("os.name", "") == "Mac OS X"
  val is_unix: Boolean = is_linux || is_macos

  def is_arm: Boolean = cpu_arch.startsWith("arm")

  def family: Family =
    if (is_linux && is_arm) Family.linux_arm
    else if (is_linux) Family.linux
    else if (is_macos) Family.macos
    else if (is_windows) Family.windows
    else error("Failed to determine current platform family")

  object Family {
    val list0: List[Family] = List(Family.linux, Family.windows, Family.macos)
    val list: List[Family] = List(Family.linux, Family.linux_arm, Family.windows, Family.macos)

    def unapply(name: String): Option[Family] =
      try { Some(Family.valueOf(name)) }
      catch { case _: IllegalArgumentException => None }

    def parse(name: String): Family =
      unapply(name) getOrElse error("Bad platform family: " + quote(name))

    val standard: Family => String =
      {
        case Family.linux_arm => "arm64-linux"
        case Family.linux => "x86_64-linux"
        case Family.macos => "x86_64-darwin"
        case Family.windows => "x86_64-cygwin"
      }

    val native: Family => String =
      {
        case Family.macos => "arm64-darwin"
        case Family.windows => "x86_64-windows"
        case platform => standard(platform)
      }
  }

  enum Family { case linux_arm, linux, macos, windows }


  /* platform identifiers */

  private val X86_64 = """amd64|x86_64""".r
  private val Arm64 = """arm64|aarch64""".r

  def cpu_arch: String =
    System.getProperty("os.arch", "") match {
      case X86_64() => "x86_64"
      case Arm64() => "arm64"
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
