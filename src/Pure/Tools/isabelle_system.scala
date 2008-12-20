/*  Title:      Pure/Tools/isabelle_system.scala
    Author:     Makarius

Isabelle system support -- basic Cygwin/Posix compatibility.
*/

package isabelle

import java.util.regex.{Pattern, Matcher}
import java.io.{BufferedReader, InputStreamReader, FileInputStream, File, IOException}

import scala.io.Source


object IsabelleSystem {

  val charset = "UTF-8"


  /* Isabelle environment settings */

  def getenv(name: String) = {
    val value = System.getenv(if (name == "HOME") "HOME_JVM" else name)
    if (value != null) value else ""
  }

  def getenv_strict(name: String) = {
    val value = getenv(name)
    if (value != "") value else error("Undefined environment variable: " + name)
  }

  def is_cygwin() = Pattern.matches(".*-cygwin", getenv_strict("ML_PLATFORM"))


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

  private def posix_prefix() = if (is_cygwin()) List(platform_path("/bin/env")) else Nil

  def exec(args: String*): Process = Runtime.getRuntime.exec((posix_prefix() ++ args).toArray)

  def exec2(args: String*): Process = {
    val cmdline = new java.util.LinkedList[String]
    for (s <- posix_prefix() ++ args) cmdline.add(s)
    new ProcessBuilder(cmdline).redirectErrorStream(true).start
  }


  /* Isabelle tools (non-interactive) */

  def isabelle_tool(args: String*) = {
    val proc =
      try { exec2((List(getenv_strict("ISABELLE_TOOL")) ++ args): _*) }
      catch { case e: IOException => error(e.getMessage) }
    proc.getOutputStream.close
    val output = Source.fromInputStream(proc.getInputStream, charset).mkString("")
    val rc = proc.waitFor
    (output, rc)
  }


  /* named pipes */

  def mk_fifo() = {
    val (result, rc) = isabelle_tool("mkfifo")
    if (rc == 0) result.trim
    else error(result)
  }

  def rm_fifo(fifo: String) = {
    val (result, rc) = isabelle_tool("rmfifo", fifo)
    if (rc != 0) error(result)
  }

  def fifo_reader(fifo: String) =  // blocks until writer is ready
    if (is_cygwin()) new BufferedReader(new InputStreamReader(Runtime.getRuntime.exec(
      Array(platform_path("/bin/cat"), fifo)).getInputStream, charset))
    else new BufferedReader(new InputStreamReader(new FileInputStream(fifo), charset))

}
