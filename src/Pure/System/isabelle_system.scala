/*  Title:      Pure/System/isabelle_system.scala
    Author:     Makarius

Isabelle system support (settings environment etc.).
*/

package isabelle

import java.util.regex.Pattern
import java.util.Locale
import java.io.{BufferedWriter, OutputStreamWriter, FileOutputStream,
  BufferedInputStream, FileInputStream, BufferedReader, InputStreamReader,
  File, IOException}
import java.awt.{GraphicsEnvironment, Font}

import scala.io.Source
import scala.util.matching.Regex
import scala.collection.mutable


class Isabelle_System(this_isabelle_home: String) extends Standard_System
{
  def this() = this(null)


  /** Isabelle environment **/

  /*
    isabelle_home precedence:
      (1) this_isabelle_home as explicit argument
      (2) ISABELLE_HOME process environment variable (e.g. inherited from running isabelle tool)
      (3) isabelle.home system property (e.g. via JVM application boot process)
  */

  private val environment: Map[String, String] =
  {
    import scala.collection.JavaConversions._

    val env0 = Map(java.lang.System.getenv.toList: _*) +
      ("THIS_JAVA" -> this_java())

    val isabelle_home =
      if (this_isabelle_home != null) this_isabelle_home
      else
        env0.get("ISABELLE_HOME") match {
          case None | Some("") =>
            val path = java.lang.System.getProperty("isabelle.home")
            if (path == null || path == "") error("Unknown Isabelle home directory")
            else path
          case Some(path) => path
        }

    Standard_System.with_tmp_file("settings") { dump =>
        val shell_prefix =
          if (Platform.is_windows) List(platform_root + "\\bin\\bash", "-l") else Nil
        val cmdline =
          shell_prefix ::: List(isabelle_home + "/bin/isabelle", "getenv", "-d", dump.toString)
        val (output, rc) = Standard_System.raw_exec(null, env0, true, cmdline: _*)
        if (rc != 0) error(output)

        val entries =
          for (entry <- Source.fromFile(dump).mkString split "\0" if entry != "") yield {
            val i = entry.indexOf('=')
            if (i <= 0) (entry -> "")
            else (entry.substring(0, i) -> entry.substring(i + 1))
          }
        Map(entries: _*) +
          ("HOME" -> java.lang.System.getenv("HOME")) +
          ("PATH" -> java.lang.System.getenv("PATH"))
      }
  }


  /* external processes */

  def execute(redirect: Boolean, args: String*): Process =
  {
    val cmdline =
      if (Platform.is_windows) List(platform_root + "\\bin\\env.exe") ++ args
      else args
    Standard_System.raw_execute(null, environment, redirect, cmdline: _*)
  }


  /* getenv */

  def getenv(name: String): String =
    environment.getOrElse(if (name == "HOME") "HOME_JVM" else name, "")

  def getenv_strict(name: String): String =
  {
    val value = getenv(name)
    if (value != "") value else error("Undefined environment variable: " + name)
  }

  override def toString = getenv("ISABELLE_HOME")



  /** file path specifications **/

  /* expand_path */

  private val Root = new Regex("(//+[^/]*|/)(.*)")
  private val Only_Root = new Regex("//+[^/]*|/")

  def expand_path(isabelle_path: String): String =
  {
    val result_path = new StringBuilder
    def init(path: String): String =
    {
      path match {
        case Root(root, rest) =>
          result_path.clear
          result_path ++= root
          rest
        case _ => path
      }
    }
    def append(path: String)
    {
      val rest = init(path)
      for (p <- rest.split("/") if p != "" && p != ".") {
        if (p == "..") {
          val result = result_path.toString
          if (!Only_Root.pattern.matcher(result).matches) {
            val i = result.lastIndexOf("/")
            if (result == "")
              result_path ++= ".."
            else if (result.substring(i + 1) == "..")
              result_path ++= "/.."
            else if (i < 0)
              result_path.length = 0
            else
              result_path.length = i
          }
        }
        else {
          val len = result_path.length
          if (len > 0 && result_path(len - 1) != '/')
            result_path += '/'
          result_path ++= p
        }
      }
    }
    val rest = init(isabelle_path)
    for (p <- rest.split("/")) {
      if (p.startsWith("$")) append(getenv_strict(p.substring(1)))
      else if (p == "~") append(getenv_strict("HOME"))
      else if (p == "~~") append(getenv_strict("ISABELLE_HOME"))
      else append(p)
    }
    result_path.toString
  }


  /* platform_path */

  def platform_path(isabelle_path: String): String =
    jvm_path(expand_path(isabelle_path))

  def platform_file(path: String) = new File(platform_path(path))


  /* try_read */

  def try_read(path: String): String =
  {
    val file = platform_file(path)
    if (file.isFile) Source.fromFile(file).mkString else ""
  }


  /* source files */

  private def try_file(file: File) = if (file.isFile) Some(file) else None

  def source_file(path: String): Option[File] =
  {
    if (path.startsWith("/") || path == "")
      try_file(platform_file(path))
    else {
      val pure_file = platform_file("$ISABELLE_HOME/src/Pure/" + path)
      if (pure_file.isFile) Some(pure_file)
      else if (getenv("ML_SOURCES") != "")
        try_file(platform_file("$ML_SOURCES/" + path))
      else None
    }
  }



  /** system tools **/

  def bash_output(script: String): (String, Int) =
  {
    Standard_System.with_tmp_file("isabelle_script") { script_file =>
      Standard_System.with_tmp_file("isabelle_pid") { pid_file =>
        Standard_System.with_tmp_file("isabelle_output") { output_file =>

          Standard_System.write_file(script_file, script)

          val proc = execute(true, expand_path("$ISABELLE_HOME/lib/scripts/bash"), "group",
            script_file.getPath, pid_file.getPath, output_file.getPath)

          def kill(strict: Boolean) =
          {
            val pid =
              try { Some(Standard_System.read_file(pid_file)) }
              catch { case _: IOException => None }
            if (pid.isDefined) {
              var running = true
              var count = 10
              while (running && count > 0) {
                if (execute(true, "kill", "-INT", "-" + pid.get).waitFor != 0)
                  running = false
                else {
                  Thread.sleep(100)
                  if (!strict) count -= 1
                }
              }
            }
          }

          val shutdown_hook = new Thread { override def run = kill(true) }
          Runtime.getRuntime.addShutdownHook(shutdown_hook)  // FIXME tmp files during shutdown?!?

          def cleanup() =
            try { Runtime.getRuntime.removeShutdownHook(shutdown_hook) }
            catch { case _: IllegalStateException => }

          val rc =
            try {
              try { proc.waitFor }  // FIXME read stderr (!??)
              catch { case e: InterruptedException => Thread.interrupted; kill(false); throw e }
            }
            finally {
              proc.getOutputStream.close
              proc.getInputStream.close
              proc.getErrorStream.close
              proc.destroy
              cleanup()
            }

          val output =
            try { Standard_System.read_file(output_file) }
            catch { case _: IOException => "" }

          (output, rc)
        }
      }
    }
  }

  def isabelle_tool(name: String, args: String*): (String, Int) =
  {
    getenv_strict("ISABELLE_TOOLS").split(":").find { dir =>
      val file = platform_file(dir + "/" + name)
      try { file.isFile && file.canRead && file.canExecute }
      catch { case _: SecurityException => false }
    } match {
      case Some(dir) =>
        Standard_System.process_output(
          execute(true, (List(expand_path(dir + "/" + name)) ++ args): _*))
      case None => ("Unknown Isabelle tool: " + name, 2)
    }
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

  def fifo_stream(fifo: String): BufferedInputStream =
  {
    // blocks until writer is ready
    val stream =
      if (Platform.is_windows) {
        val proc = execute(false, "cat", fifo)
        proc.getOutputStream.close
        proc.getErrorStream.close
        proc.getInputStream
      }
      else new FileInputStream(fifo)
    new BufferedInputStream(stream)
  }



  /** Isabelle resources **/

  /* components */

  def components(): List[String] =
    getenv("ISABELLE_COMPONENTS").split(":").toList


  /* find logics */

  def find_logics(): List[String] =
  {
    val ml_ident = getenv_strict("ML_IDENTIFIER")
    val logics = new mutable.ListBuffer[String]
    for (dir <- getenv_strict("ISABELLE_PATH").split(":")) {
      val files = platform_file(dir + "/" + ml_ident).listFiles()
      if (files != null) {
        for (file <- files if file.isFile) logics += file.getName
      }
    }
    logics.toList.sortWith(_ < _)
  }


  /* symbols */

  private def read_symbols(path: String): List[String] =
    Library.chunks(try_read(path)).map(_.toString).toList

  val symbols = new Symbol.Interpretation(
    read_symbols("$ISABELLE_HOME/etc/symbols") :::
    read_symbols("$ISABELLE_HOME_USER/etc/symbols"))


  /* fonts */

  val font_family = "IsabelleText"

  def get_font(size: Int = 1, bold: Boolean = false): Font =
    new Font(font_family, if (bold) Font.BOLD else Font.PLAIN, size)

  def install_fonts()
  {
    def create_font(bold: Boolean): Font =
    {
      val name =
        if (bold) "$ISABELLE_HOME/lib/fonts/IsabelleTextBold.ttf"
        else "$ISABELLE_HOME/lib/fonts/IsabelleText.ttf"
      Font.createFont(Font.TRUETYPE_FONT, platform_file(name))
    }
    def check_font() = get_font().getFamily == font_family

    if (!check_font()) {
      val font = create_font(false)
      val bold_font = create_font(true)

      val ge = GraphicsEnvironment.getLocalGraphicsEnvironment()
      ge.registerFont(font)
      // workaround strange problem with Apple's Java 1.6 font manager
      if (bold_font.getFamily == font_family) ge.registerFont(bold_font)
      if (!check_font()) error("Failed to install IsabelleText fonts")
    }
  }
}
