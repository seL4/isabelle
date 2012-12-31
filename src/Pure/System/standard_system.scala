/*  Title:      Pure/System/standard_system.scala
    Author:     Makarius

Standard system operations, with basic Cygwin/Posix compatibility.
*/

package isabelle

import java.lang.System
import java.util.regex.Pattern
import java.net.URL
import java.io.{File => JFile}

import scala.util.matching.Regex


object Standard_System
{
  /* cygwin_root */

  def cygwin_root(): String =
  {
    val cygwin_root1 = System.getenv("CYGWIN_ROOT")
    val cygwin_root2 = System.getProperty("cygwin.root")
    val root =
      if (cygwin_root1 != null && cygwin_root1 != "") cygwin_root1
      else if (cygwin_root2 != null && cygwin_root2 != "") cygwin_root2
      else error("Bad Cygwin installation: unknown root")

    val root_file = new JFile(root)
    if (!new JFile(root_file, "bin\\bash.exe").isFile ||
        !new JFile(root_file, "bin\\env.exe").isFile ||
        !new JFile(root_file, "bin\\tar.exe").isFile)
      error("Bad Cygwin installation: " + quote(root))

    root
  }
}


class Standard_System
{
  /* platform_root */

  val platform_root = if (Platform.is_windows) Standard_System.cygwin_root() else "/"


  /* jvm_path */

  private val Cygdrive = new Regex("/cygdrive/([a-zA-Z])($|/.*)")
  private val Named_Root = new Regex("//+([^/]*)(.*)")

  def jvm_path(posix_path: String): String =
    if (Platform.is_windows) {
      val result_path = new StringBuilder
      val rest =
        posix_path match {
          case Cygdrive(drive, rest) =>
            result_path ++= (Library.uppercase(drive) + ":" + JFile.separator)
            rest
          case Named_Root(root, rest) =>
            result_path ++= JFile.separator
            result_path ++= JFile.separator
            result_path ++= root
            rest
          case path if path.startsWith("/") =>
            result_path ++= platform_root
            path
          case path => path
        }
      for (p <- space_explode('/', rest) if p != "") {
        val len = result_path.length
        if (len > 0 && result_path(len - 1) != JFile.separatorChar)
          result_path += JFile.separatorChar
        result_path ++= p
      }
      result_path.toString
    }
    else posix_path


  /* posix_path */

  private val Platform_Root = new Regex("(?i)" +
    Pattern.quote(platform_root) + """(?:\\+|\z)(.*)""")

  private val Drive = new Regex("""([a-zA-Z]):\\*(.*)""")

  def posix_path(jvm_path: String): String =
    if (Platform.is_windows) {
      jvm_path.replace('/', '\\') match {
        case Platform_Root(rest) => "/" + rest.replace('\\', '/')
        case Drive(letter, rest) =>
          "/cygdrive/" + Library.lowercase(letter) +
            (if (rest == "") "" else "/" + rest.replace('\\', '/'))
        case path => path.replace('\\', '/')
      }
    }
    else jvm_path


  /* JDK home of running JVM */

  def this_jdk_home(): String =
  {
    val java_home = System.getProperty("java.home")
    val home = new JFile(java_home)
    val parent = home.getParent
    val jdk_home =
      if (home.getName == "jre" && parent != null &&
          (new JFile(new JFile(parent, "bin"), "javac")).exists) parent
      else java_home
    posix_path(jdk_home)
  }
}
