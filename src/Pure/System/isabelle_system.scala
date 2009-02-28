/*  Title:      Pure/Tools/isabelle_system.scala
    Author:     Makarius

Isabelle system support -- basic Cygwin/Posix compatibility.
*/

package isabelle

import java.util.regex.{Pattern, Matcher}
import java.io.{BufferedReader, InputStreamReader, FileInputStream, File, IOException}

import scala.io.Source


class IsabelleSystem {

  val charset = "UTF-8"


  /* Isabelle environment settings */

  private val environment = System.getenv

  def getenv(name: String) = {
    val value = environment.get(if (name == "HOME") "HOME_JVM" else name)
    if (value != null) value else ""
  }

  def getenv_strict(name: String) = {
    val value = environment.get(name)
    if (value != "") value else error("Undefined environment variable: " + name)
  }

  val is_cygwin = Pattern.matches(".*-cygwin", getenv_strict("ML_PLATFORM"))


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

  def platform_file(path: String) =
    new File(platform_path(path))


  /* processes */

  def execute(redirect: Boolean, args: String*): Process = {
    val cmdline = new java.util.LinkedList[String]
    if (is_cygwin) cmdline.add(platform_path("/bin/env"))
    for (s <- args) cmdline.add(s)

    val proc = new ProcessBuilder(cmdline)
    proc.environment.clear
    proc.environment.putAll(environment)
    proc.redirectErrorStream(redirect)
    proc.start
  }


  /* Isabelle tools (non-interactive) */

  def isabelle_tool(args: String*) = {
    val proc =
      try { execute(true, (List(getenv_strict("ISABELLE_TOOL")) ++ args): _*) }
      catch { case e: IOException => error(e.getMessage) }
    proc.getOutputStream.close
    val output = Source.fromInputStream(proc.getInputStream, charset).mkString
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

  def fifo_reader(fifo: String) = {
    // blocks until writer is ready
    val stream =
      if (is_cygwin) execute(false, "cat", fifo).getInputStream
      else new FileInputStream(fifo)
    new BufferedReader(new InputStreamReader(stream, charset))
  }


  /* find logics */

  def find_logics() = {
    val ml_ident = getenv_strict("ML_IDENTIFIER")
    var logics: Set[String] = Set()
    for (dir <- getenv_strict("ISABELLE_PATH").split(":")) {
      val files = platform_file(dir + "/" + ml_ident).listFiles()
      if (files != null) {
        for (file <- files if file.isFile) logics += file.getName
      }
    }
    logics.toList.sort(_ < _)
  }


  /* symbols */

  private def read_symbols(path: String) = {
    val file = new File(platform_path(path))
    if (file.canRead) Source.fromFile(file).getLines
    else Iterator.empty
  }
  val symbols = new Symbol.Interpretation(
    read_symbols("$ISABELLE_HOME/etc/symbols") ++
    read_symbols("$ISABELLE_HOME_USER/etc/symbols"))
}
