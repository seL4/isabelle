/*  Title:      Pure/System/platform.scala
    Author:     Makarius

Raw platform identification.
*/

package isabelle

import scala.util.matching.Regex


object Platform
{
  val is_macos = System.getProperty("os.name") == "Mac OS X"
  val is_windows = System.getProperty("os.name").startsWith("Windows")

  private val Solaris = new Regex("SunOS|Solaris")
  private val Linux = new Regex("Linux")
  private val Darwin = new Regex("Mac OS X")
  private val Cygwin = new Regex("Windows.*")

  private val X86 = new Regex("i.86|x86")
  private val X86_64 = new Regex("amd64|x86_64")
  private val Sparc = new Regex("sparc")
  private val PPC = new Regex("PowerPC|ppc")

  // main default, optional 64bit variant
  val defaults: Option[(String, Option[String])] =
  {
    (java.lang.System.getProperty("os.name") match {
      case Solaris() => Some("solaris")
      case Linux() => Some("linux")
      case Darwin() => Some("darwin")
      case Cygwin() => Some("cygwin")
      case _ => None
    }) match {
      case Some(name) =>
        java.lang.System.getProperty("os.arch") match {
          case X86() => Some(("x86-" + name, None))
          case X86_64() => Some(("x86-" + name, if (is_windows) None else Some("x86_64-" + name)))
          case Sparc() => Some(("sparc-" + name, None))
          case PPC() => Some(("ppc-" + name, None))
        }
      case None => None
    }
  }
}

