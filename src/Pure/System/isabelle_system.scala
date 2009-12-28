/*  Title:      Pure/System/isabelle_system.scala
    Author:     Makarius

Isabelle system support, with basic Cygwin/Posix compatibility.
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


object Isabelle_System
{
  val charset = "UTF-8"


  /* permissive UTF-8 decoding */

  // see also http://en.wikipedia.org/wiki/UTF-8#Description
  def decode_permissive_utf8(text: CharSequence): String =
  {
    val buf = new java.lang.StringBuilder(text.length)
    var code = -1
    var rest = 0
    def flush()
    {
      if (code != -1) {
        if (rest == 0 && Character.isValidCodePoint(code))
          buf.appendCodePoint(code)
        else buf.append('\uFFFD')
        code = -1
        rest = 0
      }
    }
    def init(x: Int, n: Int)
    {
      flush()
      code = x
      rest = n
    }
    def push(x: Int)
    {
      if (rest <= 0) init(x, -1)
      else {
        code <<= 6
        code += x
        rest -= 1
      }
    }
    for (i <- 0 until text.length) {
      val c = text.charAt(i)
      if (c < 128) { flush(); buf.append(c) }
      else if ((c & 0xC0) == 0x80) push(c & 0x3F)
      else if ((c & 0xE0) == 0xC0) init(c & 0x1F, 1)
      else if ((c & 0xF0) == 0xE0) init(c & 0x0F, 2)
      else if ((c & 0xF8) == 0xF0) init(c & 0x07, 3)
    }
    flush()
    buf.toString
  }


  /* basic file operations */

  def with_tmp_file[A](prefix: String)(body: File => A): A =
  {
    val file = File.createTempFile(prefix, null)
    val result =
      try { body(file) }
      finally { file.delete }
    result
  }

  def read_file(file: File): String =
  {
    val buf = new StringBuilder(file.length.toInt)
    val reader = new BufferedReader(new InputStreamReader(new FileInputStream(file), charset))
    var c = reader.read
    while (c != -1) {
      buf.append(c.toChar)
      c = reader.read
    }
    reader.close
    buf.toString
  }

  def write_file(file: File, text: CharSequence)
  {
    val writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file), charset))
    try { writer.append(text) }
    finally { writer.close }
  }


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
    val rc =
      try { proc.waitFor }
      finally {
        proc.getInputStream.close
        proc.getErrorStream.close
        proc.destroy
        Thread.interrupted
      }
    (output, rc)
  }
}


class Isabelle_System
{
  /** Isabelle environment **/

  /* platform prefixes */

  private val (platform_root, drive_prefix, shell_prefix) =
  {
    if (Platform.is_windows) {
      val root = Cygwin.check_root()
      val drive = "/cygdrive"
      val shell = List(root + "\\bin\\bash", "-l")
      (root, drive, shell)
    }
    else ("/", "", Nil)
  }


  /* bash environment */

  private val environment: Map[String, String] =
  {
    import scala.collection.jcl.Conversions._

    val env0 = Map(java.lang.System.getenv.toList: _*)

    val isabelle_home =
      env0.get("ISABELLE_HOME") match {
        case None | Some("") =>
          val path = java.lang.System.getProperty("isabelle.home")
          if (path == null || path == "") error("Unknown Isabelle home directory")
          else path
        case Some(path) => path
      }

    Isabelle_System.with_tmp_file("isabelle_settings") { dump =>
      val cmdline = shell_prefix :::
        List(isabelle_home + "/bin/isabelle", "getenv", "-d", dump.toString)
      val (output, rc) =
        Isabelle_System.process_output(Isabelle_System.raw_execute(env0, true, cmdline: _*))
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

  def expand_path(isabelle_path: String): String =
  {
    val result_path = new StringBuilder
    def init(path: String)
    {
      if (path.startsWith("/")) {
        result_path.clear
        result_path += '/'
      }
    }
    def append(path: String)
    {
      init(path)
      for (p <- path.split("/") if p != "" && p != ".") {
        if (p == "..") {
          val result = result_path.toString
          val i = result.lastIndexOf("/")
          if (result == "")
            result_path ++= ".."
          else if (result.substring(i + 1) == "..")
            result_path ++= "/.."
          else if (i < 1)
            result_path.length = i + 1
          else
            result_path.length = i
        }
        else {
          val len = result_path.length
          if (len > 0 && result_path(len - 1) != '/')
            result_path += '/'
          result_path ++= p
        }
      }
    }
    init(isabelle_path)
    for (p <- isabelle_path.split("/")) {
      if (p.startsWith("$")) append(getenv_strict(p.substring(1)))
      else if (p == "~") append(getenv_strict("HOME"))
      else if (p == "~~") append(getenv_strict("ISABELLE_HOME"))
      else append(p)
    }
    result_path.toString
  }


  /* platform_path */

  private val Cygdrive =
    new Regex(Pattern.quote(drive_prefix) + "/([a-zA-Z])($|/.*)")

  def platform_path(isabelle_path: String): String =
  {
    val result_path = new StringBuilder
    val rest =
      expand_path(isabelle_path) match {
        case Cygdrive(drive, rest) if Platform.is_windows =>
          result_path ++= (drive + ":" + File.separator)
          rest
        case path if path.startsWith("/") =>
          result_path ++= platform_root
          path
        case path => path
      }
    for (p <- rest.split("/") if p != "") {
      val len = result_path.length
      if (len > 0 && result_path(len - 1) != File.separatorChar)
        result_path += File.separatorChar
      result_path ++= p
    }
    result_path.toString
  }

  def platform_file(path: String) = new File(platform_path(path))


  /* isabelle_path */

  private val Platform_Root = new Regex("(?i)" +
    Pattern.quote(platform_root) + """(?:\\+|\z)(.*)""")
  private val Drive = new Regex("""([a-zA-Z]):\\*(.*)""")

  def isabelle_path(platform_path: String): String =
  {
    if (Platform.is_windows) {
      platform_path.replace('/', '\\') match {
        case Platform_Root(rest) => "/" + rest.replace('\\', '/')
        case Drive(letter, rest) =>
          drive_prefix + "/" + letter.toLowerCase(Locale.ENGLISH) +
            (if (rest == "") "" else "/" + rest.replace('\\', '/'))
        case path => path.replace('\\', '/')
      }
    }
    else platform_path
  }


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



  /** system tools **/

  /* external processes */

  def execute(redirect: Boolean, args: String*): Process =
  {
    val cmdline =
      if (Platform.is_windows) List(platform_path("/bin/env")) ++ args
      else args
    Isabelle_System.raw_execute(environment, redirect, cmdline: _*)
  }

  def system_out(script: String): (String, Int) =
  {
    Isabelle_System.with_tmp_file("isabelle_script") { script_file =>
      Isabelle_System.with_tmp_file("isabelle_pid") { pid_file =>
        Isabelle_System.with_tmp_file("isabelle_output") { output_file =>

          Isabelle_System.write_file(script_file, script)

          val proc = execute(true, "perl", "-w",
            expand_path("$ISABELLE_HOME/lib/scripts/system.pl"), "group",
            script_file.getPath, pid_file.getPath, output_file.getPath)

          def kill(strict: Boolean) =
          {
            val pid =
              try { Some(Isabelle_System.read_file(pid_file)) }
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
          Runtime.getRuntime.addShutdownHook(shutdown_hook)

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
            try { Isabelle_System.read_file(output_file) }
            catch { case _: IOException => "" }

          (output, rc)
        }
      }
    }
  }

  def isabelle_tool(name: String, args: String*): (String, Int) =
  {
    getenv_strict("ISABELLE_TOOLS").split(":").find(dir => {
      val file = platform_file(dir + "/" + name)
      try { file.isFile && file.canRead && file.canExecute }
      catch { case _: SecurityException => false }
    }) match {
      case Some(dir) =>
        Isabelle_System.process_output(
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
    logics.toList.sort(_ < _)
  }


  /* symbols */

  private def read_symbols(path: String): List[String] =
  {
    val file = platform_file(path)
    if (file.isFile) Source.fromFile(file).getLines.toList
    else Nil
  }
  val symbols = new Symbol.Interpretation(
    read_symbols("$ISABELLE_HOME/etc/symbols") :::
    read_symbols("$ISABELLE_HOME_USER/etc/symbols"))


  /* fonts */

  val font_family = "IsabelleText"

  private def check_font(): Boolean =
    new Font(font_family, Font.PLAIN, 1).getFamily == font_family

  private def create_font(name: String) =
    Font.createFont(Font.TRUETYPE_FONT, platform_file(name))

  def install_fonts()
  {
    if (!check_font()) {
      val ge = GraphicsEnvironment.getLocalGraphicsEnvironment()
      ge.registerFont(create_font("$ISABELLE_HOME/lib/fonts/IsabelleText.ttf"))
      ge.registerFont(create_font("$ISABELLE_HOME/lib/fonts/IsabelleTextBold.ttf"))
      if (!check_font())
        error("Failed to install IsabelleText fonts")
    }
  }
}
