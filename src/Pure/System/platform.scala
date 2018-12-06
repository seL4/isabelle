/*  Title:      Pure/System/platform.scala
    Author:     Makarius

System platform identification.
*/

package isabelle


object Platform
{
  /* platform family */

  val is_linux = System.getProperty("os.name", "") == "Linux"
  val is_macos = System.getProperty("os.name", "") == "Mac OS X"
  val is_windows = System.getProperty("os.name", "").startsWith("Windows")

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

  private val Linux = """Linux""".r
  private val Darwin = """Mac OS X""".r
  private val Windows = """Windows.*""".r

  private val X86 = """i.86|x86""".r
  private val X86_64 = """amd64|x86_64""".r

  lazy val jvm_platform: String =
  {
    val arch =
      System.getProperty("os.arch", "") match {
        case X86() => "x86"
        case X86_64() => "x86_64"
        case _ => error("Failed to determine CPU architecture")
      }
    val os =
      System.getProperty("os.name", "") match {
        case Linux() => "linux"
        case Darwin() => "darwin"
        case Windows() => "windows"
        case _ => error("Failed to determine operating system platform")
      }
    arch + "-" + os
  }


  /* JVM version */

  private val Version = """1\.(\d+)\.0_(\d+)""".r
  lazy val jvm_version =
    System.getProperty("java.version") match {
      case Version(a, b) => a + "u" + b
      case a => a
    }


  /* JVM name */

  val jvm_name: String = System.getProperty("java.vm.name", "")
}
