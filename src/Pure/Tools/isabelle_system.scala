/*  Title:      Pure/Tools/isabelle_system.scala
    ID:         $Id$
    Author:     Makarius

Isabelle system support -- basic Cygwin/Posix compatibility.
*/

package isabelle

import java.util.regex.{Pattern, Matcher}
import java.io.File


object IsabelleSystem {

  /* Isabelle settings */

  def getenv(name: String) = {
    val value = System.getenv(name)
    if (value != null) value else ""
  }

  class BadVariable(val name: String) extends Exception {
    override def toString = "BadVariable: " + name
  }

  def getenv_strict(name: String) = {
    val value = getenv(name)
    if (value != "") value else throw new BadVariable(name)
  }


  /* file path specifications */

  private val cygdrive_pattern = Pattern.compile("/cygdrive/([a-zA-Z])($|/.*)")

  def platform_path(source_path: String) = {
    val result_path = new StringBuilder

    def init(path: String) = {
      val cygdrive = cygdrive_pattern.matcher(path)
      if (cygdrive.matches) {
        result_path.length = 0
        result_path.append(cygdrive.group(1))
        result_path.append(":")
        result_path.append(File.separator)
        cygdrive.group(2)
      }
      else if (path.startsWith("/")) {
        result_path.length = 0
        result_path.append(getenv_strict("ISABELLE_ROOT_JVM"))
        path.substring(1)
      }
      else path
    }
    def append(path: String) = {
      for (p <- init(path).split("/")) {
        if (p != "") {
          val len = result_path.length
          if (len > 0 && result_path(len - 1) != File.separatorChar)
            result_path.append(File.separator)
          result_path.append(p)
        }
      }
    }
    for (p <- init(source_path).split("/")) {
      if (p.startsWith("$")) append(getenv_strict(p.substring(1)))
      else if (p == "~") append(getenv_strict("HOME"))
      else if (p == "~~") append(getenv_strict("ISABELLE_HOME"))
      else append(p)
    }
    result_path.toString
  }


  /* processes */

  private def posix_prefix() = {
    if (Pattern.matches(".*-cygwin", getenv_strict("ML_PLATFORM")))
      List(platform_path("/bin/env"))
    else Nil
  }

  def exec(args: List[String]) = Runtime.getRuntime.exec((posix_prefix() ++ args).toArray)

}
