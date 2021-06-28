/*  Title:      Pure/System/isabelle_env.scala
    Author:     Makarius

Fundamental Isabelle system environment: quasi-static module with
optional init operation.
*/

package isabelle


import java.io.{File => JFile}

import scala.jdk.CollectionConverters._



object Isabelle_Env
{
  /** bootstrap information **/

  def jdk_home(): String =
  {
    val java_home = System.getProperty("java.home", "")
    val home = new JFile(java_home)
    val parent = home.getParent
    if (home.getName == "jre" && parent != null &&
        (new JFile(new JFile(parent, "bin"), "javac")).exists) parent
    else java_home
  }

  def bootstrap_directory(
    preference: String, envar: String, property: String, description: String): String =
  {
    val value =
      proper_string(preference) orElse  // explicit argument
      proper_string(System.getenv(envar)) orElse  // e.g. inherited from running isabelle tool
      proper_string(System.getProperty(property)) getOrElse  // e.g. via JVM application boot process
      error("Unknown " + description + " directory")

    if ((new JFile(value)).isDirectory) value
    else error("Bad " + description + " directory " + quote(value))
  }



  /** raw process **/

  /* raw process */

  def process(command_line: List[String],
    cwd: JFile = null,
    env: Map[String, String] = settings(),
    redirect: Boolean = false): Process =
  {
    val proc = new ProcessBuilder

    // fragile on Windows:
    // see https://docs.microsoft.com/en-us/cpp/cpp/main-function-command-line-args?view=msvc-160
    proc.command(command_line.asJava)

    if (cwd != null) proc.directory(cwd)
    if (env != null) {
      proc.environment.clear()
      for ((x, y) <- env) proc.environment.put(x, y)
    }
    proc.redirectErrorStream(redirect)
    proc.start
  }

  def process_output(proc: Process): (String, Int) =
  {
    proc.getOutputStream.close()

    val output = File.read_stream(proc.getInputStream)
    val rc =
      try { proc.waitFor }
      finally {
        proc.getInputStream.close()
        proc.getErrorStream.close()
        proc.destroy()
        Exn.Interrupt.dispose()
      }
    (output, rc)
  }



  /** implicit settings environment **/

  abstract class Service

  @volatile private var _settings: Option[Map[String, String]] = None
  @volatile private var _services: Option[List[Class[Service]]] = None

  def settings(): Map[String, String] =
  {
    if (_settings.isEmpty) init()  // unsynchronized check
    _settings.get
  }

  def services(): List[Class[Service]] =
  {
    if (_services.isEmpty) init()  // unsynchronized check
    _services.get
  }

  def getenv_error(name: String): Nothing =
    error("Undefined Isabelle environment variable: " + quote(name))

  def init(isabelle_root: String = "", cygwin_root: String = ""): Unit = synchronized
  {
    if (_settings.isEmpty || _services.isEmpty) {
      val isabelle_root1 =
        bootstrap_directory(isabelle_root, "ISABELLE_ROOT", "isabelle.root", "Isabelle root")

      val cygwin_root1 =
        if (Platform.is_windows)
          bootstrap_directory(cygwin_root, "CYGWIN_ROOT", "cygwin.root", "Cygwin root")
        else ""

      if (Platform.is_windows) Cygwin.init(isabelle_root1, cygwin_root1)

      def set_cygwin_root(): Unit =
      {
        if (Platform.is_windows)
          _settings = Some(_settings.getOrElse(Map.empty) + ("CYGWIN_ROOT" -> cygwin_root1))
      }

      set_cygwin_root()

      def default(env: Map[String, String], entry: (String, String)): Map[String, String] =
        if (env.isDefinedAt(entry._1) || entry._2 == "") env
        else env + entry

      val env =
      {
        val temp_windows =
        {
          val temp = if (Platform.is_windows) System.getenv("TEMP") else null
          if (temp != null && temp.contains('\\')) temp else ""
        }
        val user_home = System.getProperty("user.home", "")
        val isabelle_app = System.getProperty("isabelle.app", "")

        default(
          default(
            default(sys.env + ("ISABELLE_JDK_HOME" -> File.standard_path(jdk_home())),
              "TEMP_WINDOWS" -> temp_windows),
            "HOME" -> user_home),
          "ISABELLE_APP" -> isabelle_app)
      }

      val settings =
      {
        val dump = JFile.createTempFile("settings", null)
        dump.deleteOnExit
        try {
          val cmd1 =
            if (Platform.is_windows)
              List(cygwin_root1 + "\\bin\\bash", "-l",
                File.standard_path(isabelle_root1 + "\\bin\\isabelle"))
            else
              List(isabelle_root1 + "/bin/isabelle")
          val cmd = cmd1 ::: List("getenv", "-d", dump.toString)

          val (output, rc) = process_output(process(cmd, env = env, redirect = true))
          if (rc != 0) error(output)

          val entries =
            space_explode('\u0000', File.read(dump)).flatMap(
              {
                case Properties.Eq(a, b) => Some(a -> b)
                case s => if (s.isEmpty || s.startsWith("=")) None else Some(s -> "")
              }).toMap
          entries + ("PATH" -> entries("PATH_JVM")) - "PATH_JVM"
        }
        finally { dump.delete }
      }
      _settings = Some(settings)
      set_cygwin_root()

      val variable = "ISABELLE_SCALA_SERVICES"
      val services =
        for (name <- space_explode(':', settings.getOrElse(variable, getenv_error(variable))))
        yield {
          def err(msg: String): Nothing =
            error("Bad entry " + quote(name) + " in " + variable + "\n" + msg)
          try { Class.forName(name).asInstanceOf[Class[Service]] }
          catch {
            case _: ClassNotFoundException => err("Class not found")
            case exn: Throwable => err(Exn.message(exn))
          }
        }
      _services = Some(services)
    }
  }
}
