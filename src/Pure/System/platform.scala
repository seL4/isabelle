/*  Title:      Pure/System/platform.scala
    Module:     PIDE
    Author:     Makarius

Raw platform identification.
*/

package isabelle

import java.lang.System
import javax.swing.UIManager

import scala.util.matching.Regex


object Platform
{
  /* main OS variants */

  val is_macos = System.getProperty("os.name") == "Mac OS X"
  val is_windows = System.getProperty("os.name").startsWith("Windows")


  /* Platform identifiers */

  private val Solaris = new Regex("SunOS|Solaris")
  private val Linux = new Regex("Linux")
  private val Darwin = new Regex("Mac OS X")
  private val Windows = new Regex("Windows.*")

  private val X86 = new Regex("i.86|x86")
  private val X86_64 = new Regex("amd64|x86_64")
  private val Sparc = new Regex("sparc")
  private val PPC = new Regex("PowerPC|ppc")

  lazy val jvm_platform: String =
  {
    val arch =
      System.getProperty("os.arch") match {
        case X86() => "x86"
        case X86_64() => "x86_64"
        case Sparc() => "sparc"
        case PPC() => "ppc"
        case _ => error("Failed to determine CPU architecture")
      }
    val os =
      System.getProperty("os.name") match {
        case Solaris() => "solaris"
        case Linux() => "linux"
        case Darwin() => "darwin"
        case Windows() => "windows"
        case _ => error("Failed to determine operating system platform")
      }
    arch + "-" + os
  }


  /* JVM name */

  val jvm_name: String = System.getProperty("java.vm.name")


  /* Swing look-and-feel */

  private def find_laf(name: String): Option[String] =
    UIManager.getInstalledLookAndFeels().find(_.getName == name).map(_.getClassName)

  def get_laf(): String =
  {
    if (is_windows || is_macos) UIManager.getSystemLookAndFeelClassName()
    else
      find_laf("Nimbus") orElse find_laf("GTK+") getOrElse
      UIManager.getCrossPlatformLookAndFeelClassName()
  }

  def init_laf(): Unit = UIManager.setLookAndFeel(get_laf())
}

