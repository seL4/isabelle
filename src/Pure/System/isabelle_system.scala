/*  Title:      Pure/System/isabelle_system.scala
    Author:     Makarius

Isabelle system support -- basic Cygwin/Posix compatibility.
*/

package isabelle

import java.util.regex.Pattern
import java.io.{BufferedReader, InputStreamReader, FileInputStream, File, IOException}

import scala.io.Source
import scala.util.matching.Regex


object IsabelleSystem
{

  val charset = "UTF-8"

  val is_cygwin = System.getProperty("os.name").startsWith("Windows")


  /* shell processes */

  private def raw_execute(env: Map[String, String], redirect: Boolean, args: String*): Process =
  {
    val cmdline = new java.util.LinkedList[String]
    for (s <- args) cmdline.add(s)

    val proc = new ProcessBuilder(cmdline)
    proc.environment.clear
    for ((x, y) <- env) proc.environment.put(x, y)
    proc.redirectErrorStream(redirect)

    try { proc.start }
    catch { case e: IOException => error(e.getMessage) }
  }

  private def process_output(proc: Process): (String, Int) =
  {
    proc.getOutputStream.close
    val output = Source.fromInputStream(proc.getInputStream, charset).mkString
    val rc = proc.waitFor
    (output, rc)
  }

}


class IsabelleSystem
{

  /* unique ids */

  private var id_count: BigInt = 0
  def id(): String = synchronized { id_count += 1; "j" + id_count }


  /* Isabelle settings environment */

  private val (platform_root, drive_prefix, shell_prefix) =
  {
    if (IsabelleSystem.is_cygwin) {
      val root = Cygwin.root() getOrElse "C:\\cygwin"
      val drive = Cygwin.cygdrive() getOrElse "/cygdrive"
      val shell = List(root + "\\bin\\bash", "-l")
      (root, drive, shell)
    }
    else ("/", "", Nil)
  }

  private val environment: Map[String, String] =
  {
    import scala.collection.jcl.Conversions._

    val env0 = Map(java.lang.System.getenv.toList: _*)

    val isabelle =
      env0.get("ISABELLE_TOOL") match {
        case None | Some("") =>
          val isabelle = java.lang.System.getProperty("isabelle.tool")
          if (isabelle == null || isabelle == "") "isabelle"
          else isabelle
        case Some(isabelle) => isabelle
      }

    val dump = File.createTempFile("isabelle", null)
    try {
      val cmdline = shell_prefix ::: List(isabelle, "getenv", "-d", dump.toString)
      val proc = IsabelleSystem.raw_execute(env0, true, cmdline: _*)
      val (output, rc) = IsabelleSystem.process_output(proc)
      if (rc != 0) error(output)

      val entries =
        for (entry <- Source.fromFile(dump).mkString split "\0" if entry != "") yield {
          val i = entry.indexOf('=')
          if (i <= 0) (entry -> "")
          else (entry.substring(0, i) -> entry.substring(i + 1))
        }
      Map(entries: _*)
    }
    finally { dump.delete }
  }

  def getenv(name: String): String =
  {
    environment.getOrElse(if (name == "HOME") "HOME_JVM" else name, "")
  }

  def getenv_strict(name: String): String =
  {
    val value = getenv(name)
    if (value != "") value else error("Undefined environment variable: " + name)
  }

  override def toString = getenv("ISABELLE_HOME")


  /* file path specifications */

  private val Cygdrive = new Regex(
    if (drive_prefix == "") "\0"
    else Pattern.quote(drive_prefix) + "/([a-zA-Z])($|/.*)")

  def platform_path(source_path: String): String =
  {
    val result_path = new StringBuilder

    def init(path: String): String =
    {
      path match {
        case Cygdrive(drive, rest) =>
          result_path.length = 0
          result_path.append(drive)
          result_path.append(":")
          result_path.append(File.separator)
          rest
        case _ if (path.startsWith("/")) =>
          result_path.length = 0
          result_path.append(platform_root)
          path.substring(1)
        case _ => path
      }
    }
    def append(path: String)
    {
      for (p <- init(path) split "/") {
        if (p != "") {
          val len = result_path.length
          if (len > 0 && result_path(len - 1) != File.separatorChar)
            result_path.append(File.separator)
          result_path.append(p)
        }
      }
    }
    for (p <- init(source_path) split "/") {
      if (p.startsWith("$")) append(getenv_strict(p.substring(1)))
      else if (p == "~") append(getenv_strict("HOME"))
      else if (p == "~~") append(getenv_strict("ISABELLE_HOME"))
      else append(p)
    }
    result_path.toString
  }

  def platform_file(path: String) = new File(platform_path(path))


  /* source files */

  private def try_file(file: File) = if (file.isFile) Some(file) else None

  def source_file(path: String): Option[File] =
  {
    if (path.startsWith("/") || path == "")
      try_file(platform_file(path))
    else {
      val pure_file = platform_file("~~/src/Pure/" + path)
      if (pure_file.isFile) Some(pure_file)
      else if (getenv("ML_SOURCES") != "")
        try_file(platform_file("$ML_SOURCES/" + path))
      else None
    }
  }


  /* external processes */

  def execute(redirect: Boolean, args: String*): Process =
  {
    val cmdline =
      if (IsabelleSystem.is_cygwin) List(platform_path("/bin/env")) ++ args
      else args
    IsabelleSystem.raw_execute(environment, redirect, cmdline: _*)
  }

  def isabelle_tool(args: String*): (String, Int) =
  {
    val proc = execute(true, (List(getenv_strict("ISABELLE_TOOL")) ++ args): _*)
    IsabelleSystem.process_output(proc)
  }


  /* named pipes */

  def mk_fifo(): String =
  {
    val (result, rc) = isabelle_tool("mkfifo")
    if (rc == 0) result.trim
    else error(result)
  }

  def rm_fifo(fifo: String)
  {
    val (result, rc) = isabelle_tool("rmfifo", fifo)
    if (rc != 0) error(result)
  }

  def fifo_reader(fifo: String): BufferedReader =
  {
    // blocks until writer is ready
    val stream =
      if (IsabelleSystem.is_cygwin) execute(false, "cat", fifo).getInputStream
      else new FileInputStream(fifo)
    new BufferedReader(new InputStreamReader(stream, IsabelleSystem.charset))
  }


  /* find logics */

  def find_logics(): List[String] =
  {
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

  private def read_symbols(path: String): Iterator[String] =
  {
    val file = new File(platform_path(path))
    if (file.isFile) Source.fromFile(file).getLines
    else Iterator.empty
  }
  val symbols = new Symbol.Interpretation(
    read_symbols("$ISABELLE_HOME/etc/symbols") ++
    read_symbols("$ISABELLE_HOME_USER/etc/symbols"))
}
