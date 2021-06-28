/*  Title:      Pure/System/isabelle_env.scala
    Author:     Makarius

Fundamental Isabelle system environment: quasi-static module with
optional init operation.
*/

package isabelle


import java.util.{LinkedList, List => JList}
import java.io.{File => JFile}
import java.nio.file.Files
import scala.annotation.tailrec


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



  /** Support for Cygwin as POSIX emulation on Windows **/

  /* symlink emulation */

  def cygwin_link(content: String, target: JFile): Unit =
  {
    val target_path = target.toPath
    Files.writeString(target_path, "!<symlink>" + content + "\u0000")
    Files.setAttribute(target_path, "dos:system", true)
  }


  /* init (e.g. after extraction via 7zip) */

  def cygwin_init(isabelle_root: String, cygwin_root: String): Unit =
  {
    require(Platform.is_windows, "Windows platform expected")

    def cygwin_exec(cmd: JList[String]): Unit =
    {
      val cwd = new JFile(isabelle_root)
      val env = sys.env + ("CYGWIN" -> "nodosfilewarning")
      val res = exec_process(cmd, cwd = cwd, env = env, redirect = true)
      if (!res.ok) error(res.out)
    }

    val uninitialized_file = new JFile(cygwin_root, "isabelle\\uninitialized")
    val uninitialized = uninitialized_file.isFile && uninitialized_file.delete

    if (uninitialized) {
      val symlinks =
      {
        val path = (new JFile(cygwin_root + "\\isabelle\\symlinks")).toPath
        Files.readAllLines(path, UTF8.charset).toArray.toList.asInstanceOf[List[String]]
      }
      @tailrec def recover_symlinks(list: List[String]): Unit =
      {
        list match {
          case Nil | List("") =>
          case target :: content :: rest =>
            cygwin_link(content, new JFile(isabelle_root, target))
            recover_symlinks(rest)
          case _ => error("Unbalanced symlinks list")
        }
      }
      recover_symlinks(symlinks)

      cygwin_exec(JList.of(cygwin_root + "\\bin\\dash.exe", "/isabelle/rebaseall"))
      cygwin_exec(JList.of(cygwin_root + "\\bin\\bash.exe", "/isabelle/postinstall"))
    }
  }



  /** raw process **/

  /* raw process */

  def process_builder(cmd: JList[String],
    cwd: JFile = null,
    env: Map[String, String] = settings(),
    redirect: Boolean = false): ProcessBuilder =
  {
    val builder = new ProcessBuilder

    // fragile on Windows:
    // see https://docs.microsoft.com/en-us/cpp/cpp/main-function-command-line-args?view=msvc-160
    builder.command(cmd)

    if (cwd != null) builder.directory(cwd)
    if (env != null) {
      builder.environment.clear()
      for ((x, y) <- env) builder.environment.put(x, y)
    }
    builder.redirectErrorStream(redirect)
  }

  class Exec_Result(val rc: Int, val out: String, val err: String)
  {
    def ok: Boolean = rc == 0
  }

  def exec_process(command_line: JList[String],
    cwd: JFile = null,
    env: Map[String, String] = settings(),
    redirect: Boolean = false): Exec_Result =
  {
    val out_file = Files.createTempFile(null, null)
    val err_file = Files.createTempFile(null, null)
    try {
      val proc =
      {
        val builder = process_builder(command_line, cwd = cwd, env = env, redirect = redirect)
        builder.redirectOutput(out_file.toFile)
        builder.redirectError(err_file.toFile)
        builder.start()
      }
      proc.getOutputStream.close()
      try { proc.waitFor() }
      finally {
        proc.getInputStream.close()
        proc.getErrorStream.close()
        proc.destroy()
        Thread.interrupted()
      }

      val rc = proc.exitValue()
      val out = Files.readString(out_file)
      val err = Files.readString(err_file)
      new Exec_Result(rc, out, err)
    }
    finally {
      Files.deleteIfExists(out_file)
      Files.deleteIfExists(err_file)
    }
  }



  /** implicit settings environment **/

  @volatile private var _settings: Option[Map[String, String]] = None

  def settings(): Map[String, String] =
  {
    if (_settings.isEmpty) init("", "")  // unsynchronized check
    _settings.get
  }

  def init(isabelle_root: String, cygwin_root: String): Unit = synchronized
  {
    if (_settings.isEmpty) {
      val isabelle_root1 =
        bootstrap_directory(isabelle_root, "ISABELLE_ROOT", "isabelle.root", "Isabelle root")

      val cygwin_root1 =
        if (Platform.is_windows)
          bootstrap_directory(cygwin_root, "CYGWIN_ROOT", "cygwin.root", "Cygwin root")
        else ""

      if (Platform.is_windows) cygwin_init(isabelle_root1, cygwin_root1)

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
          val cmd = new LinkedList[String]
          if (Platform.is_windows) {
            cmd.add(cygwin_root1 + "\\bin\\bash")
            cmd.add("-l")
            cmd.add(File.standard_path(isabelle_root1 + "\\bin\\isabelle"))
          } else {
            cmd.add(isabelle_root1 + "/bin/isabelle")
          }
          cmd.add("getenv")
          cmd.add("-d")
          cmd.add(dump.toString)

          val res = exec_process(cmd, env = env, redirect = true)
          if (!res.ok) error(res.out)

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
    }
  }
}
