/*  Title:      Pure/System/isabelle_system.scala
    Author:     Makarius

Fundamental Isabelle system environment: quasi-static module with
optional init operation.
*/

package isabelle

import java.lang.System
import java.util.regex.Pattern
import java.util.Locale
import java.io.{InputStream, OutputStream, File => JFile, BufferedReader, InputStreamReader,
  BufferedWriter, OutputStreamWriter, IOException}
import java.awt.{GraphicsEnvironment, Font}
import java.awt.font.TextAttribute

import scala.io.Source
import scala.util.matching.Regex
import scala.collection.mutable


object Isabelle_System
{
  /** implicit state **/

  private case class State(standard_system: Standard_System, settings: Map[String, String])

  @volatile private var _state: Option[State] = None

  private def check_state(): State =
  {
    if (_state.isEmpty) init()  // unsynchronized check
    _state.get
  }

  def standard_system: Standard_System = check_state().standard_system
  def settings: Map[String, String] = check_state().settings

  /*
    isabelle_home precedence:
      (1) this_isabelle_home as explicit argument
      (2) ISABELLE_HOME process environment variable (e.g. inherited from running isabelle tool)
      (3) isabelle.home system property (e.g. via JVM application boot process)
  */
  def init(this_isabelle_home: String = null) = synchronized {
    if (_state.isEmpty) {
      import scala.collection.JavaConversions._

      val standard_system = new Standard_System
      val settings =
      {
        val env0 = sys.env + ("ISABELLE_JDK_HOME" -> standard_system.this_jdk_home())

        val user_home = System.getProperty("user.home")
        val env =
          if (user_home == null || env0.isDefinedAt("HOME")) env0
          else env0 + ("HOME" -> user_home)

        val isabelle_home =
          if (this_isabelle_home != null) this_isabelle_home
          else
            env.get("ISABELLE_HOME") match {
              case None | Some("") =>
                val path = System.getProperty("isabelle.home")
                if (path == null || path == "") error("Unknown Isabelle home directory")
                else path
              case Some(path) => path
            }

          File.with_tmp_file("settings") { dump =>
              val shell_prefix =
                if (Platform.is_windows) List(standard_system.platform_root + "\\bin\\bash", "-l")
                else Nil
              val cmdline =
                shell_prefix ::: List(isabelle_home + "/bin/isabelle", "getenv", "-d", dump.toString)
              val (output, rc) = Standard_System.raw_exec(null, env, true, cmdline: _*)
              if (rc != 0) error(output)

              val entries =
                (for (entry <- File.read(dump) split "\0" if entry != "") yield {
                  val i = entry.indexOf('=')
                  if (i <= 0) (entry -> "")
                  else (entry.substring(0, i) -> entry.substring(i + 1))
                }).toMap
              entries + ("PATH" -> entries("PATH_JVM")) - "PATH_JVM"
            }
          }
      _state = Some(State(standard_system, settings))
    }
  }


  /* getenv */

  def getenv(name: String): String = settings.getOrElse(name, "")

  def getenv_strict(name: String): String =
  {
    val value = getenv(name)
    if (value != "") value else error("Undefined environment variable: " + name)
  }


  /** file-system operations **/

  /* path specifications */

  def standard_path(path: Path): String = path.expand.implode

  def platform_path(path: Path): String = standard_system.jvm_path(standard_path(path))
  def platform_file(path: Path): JFile = new JFile(platform_path(path))

  def platform_file_url(raw_path: Path): String =
  {
    val path = raw_path.expand
    require(path.is_absolute)
    val s = platform_path(path).replaceAll(" ", "%20")
    if (!Platform.is_windows) "file://" + s
    else if (s.startsWith("\\\\")) "file:" + s.replace('\\', '/')
    else "file:///" + s.replace('\\', '/')
  }

  def posix_path(jvm_path: String): String = standard_system.posix_path(jvm_path)


  /* try_read */

  def try_read(paths: Seq[Path]): String =
  {
    val buf = new StringBuilder
    for {
      path <- paths
      file = platform_file(path) if file.isFile
    } { buf.append(File.read(file)); buf.append('\n') }
    buf.toString
  }


  /* source files */

  private def try_file(file: JFile) = if (file.isFile) Some(file) else None

  def source_file(path: Path): Option[JFile] =
  {
    if (path.is_absolute || path.is_current)
      try_file(platform_file(path))
    else {
      val pure_file = (Path.explode("~~/src/Pure") + path).file
      if (pure_file.isFile) Some(pure_file)
      else if (getenv("ML_SOURCES") != "") try_file((Path.explode("$ML_SOURCES") + path).file)
      else None
    }
  }



  /** external processes **/

  /* plain execute */

  def execute_env(cwd: JFile, env: Map[String, String], redirect: Boolean, args: String*): Process =
  {
    val cmdline =
      if (Platform.is_windows) List(standard_system.platform_root + "\\bin\\env.exe") ++ args
      else args
    val env1 = if (env == null) settings else settings ++ env
    Standard_System.raw_execute(cwd, env1, redirect, cmdline: _*)
  }

  def execute(redirect: Boolean, args: String*): Process =
    execute_env(null, null, redirect, args: _*)


  /* managed process */

  class Managed_Process(cwd: JFile, env: Map[String, String], redirect: Boolean, args: String*)
  {
    private val params =
      List(standard_path(Path.explode("~~/lib/scripts/process")), "group", "-", "no_script")
    private val proc = execute_env(cwd, env, redirect, (params ++ args):_*)


    // channels

    val stdin: BufferedWriter =
      new BufferedWriter(new OutputStreamWriter(proc.getOutputStream, Standard_System.charset))

    val stdout: BufferedReader =
      new BufferedReader(new InputStreamReader(proc.getInputStream, Standard_System.charset))

    val stderr: BufferedReader =
      new BufferedReader(new InputStreamReader(proc.getErrorStream, Standard_System.charset))


    // signals

    private val pid = stdout.readLine

    private def kill(signal: String): Boolean =
    {
      execute(true, "kill", "-" + signal, "-" + pid).waitFor
      execute(true, "kill", "-0", "-" + pid).waitFor == 0
    }

    private def multi_kill(signal: String): Boolean =
    {
      var running = true
      var count = 10
      while (running && count > 0) {
        if (kill(signal)) {
          Thread.sleep(100)
          count -= 1
        }
        else running = false
      }
      running
    }

    def interrupt() { multi_kill("INT") }
    def terminate() { multi_kill("INT") && multi_kill("TERM") && kill("KILL"); proc.destroy }


    // JVM shutdown hook

    private val shutdown_hook = new Thread { override def run = terminate() }

    try { Runtime.getRuntime.addShutdownHook(shutdown_hook) }
    catch { case _: IllegalStateException => }

    private def cleanup() =
      try { Runtime.getRuntime.removeShutdownHook(shutdown_hook) }
      catch { case _: IllegalStateException => }


    /* result */

    def join: Int = { val rc = proc.waitFor; cleanup(); rc }
  }


  /* bash */

  def bash_env(cwd: JFile, env: Map[String, String], script: String): (String, String, Int) =
  {
    File.with_tmp_file("isabelle_script") { script_file =>
      File.write(script_file, script)
      val proc = new Managed_Process(cwd, env, false, "bash", posix_path(script_file.getPath))

      proc.stdin.close
      val (_, stdout) = Simple_Thread.future("bash_stdout") { File.read(proc.stdout) }
      val (_, stderr) = Simple_Thread.future("bash_stderr") { File.read(proc.stderr) }

      val rc =
        try { proc.join }
        catch { case e: InterruptedException => Thread.interrupted; proc.terminate; 130 }
      (stdout.join, stderr.join, rc)
    }
  }

  def bash(script: String): (String, String, Int) = bash_env(null, null, script)


  /* system tools */

  def isabelle_tool(name: String, args: String*): (String, Int) =
  {
    Path.split(getenv_strict("ISABELLE_TOOLS")).find { dir =>
      val file = (dir + Path.basic(name)).file
      try {
        file.isFile && file.canRead && file.canExecute &&
          !name.endsWith("~") && !name.endsWith(".orig")
      }
      catch { case _: SecurityException => false }
    } match {
      case Some(dir) =>
        val file = standard_path(dir + Path.basic(name))
        Standard_System.process_output(execute(true, (List(file) ++ args): _*))
      case None => ("Unknown Isabelle tool: " + name, 2)
    }
  }



  /** Isabelle resources **/

  /* components */

  def components(): List[Path] =
    Path.split(getenv_strict("ISABELLE_COMPONENTS"))


  /* find logics */

  def find_logics(): List[String] =
  {
    val ml_ident = getenv_strict("ML_IDENTIFIER")
    val logics = new mutable.ListBuffer[String]
    for (dir <- Path.split(getenv_strict("ISABELLE_PATH"))) {
      val files = (dir + Path.explode(ml_ident)).file.listFiles()
      if (files != null) {
        for (file <- files if file.isFile) logics += file.getName
      }
    }
    logics.toList.sorted
  }


  /* fonts */

  def get_font(family: String = "IsabelleText", size: Int = 1, bold: Boolean = false): Font =
    new Font(family, if (bold) Font.BOLD else Font.PLAIN, size)

  def install_fonts()
  {
    val ge = GraphicsEnvironment.getLocalGraphicsEnvironment()
    for (font <- Path.split(getenv_strict("ISABELLE_FONTS")))
      ge.registerFont(Font.createFont(Font.TRUETYPE_FONT, font.file))
  }
}
