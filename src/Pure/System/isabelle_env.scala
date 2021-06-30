/*  Title:      Pure/System/isabelle_env.scala
    Author:     Makarius

Fundamental Isabelle system environment: quasi-static module with
optional init operation.
*/

package isabelle


import java.util.{HashMap, LinkedList, List => JList, Map => JMap}
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
    if (Platform.is_windows) {
      def cygwin_exec(cmd: JList[String]): Unit =
      {
        val cwd = new JFile(isabelle_root)
        val env = new HashMap(System.getenv())
        env.put("CYGWIN", "nodosfilewarning")
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
  }



  /** raw process **/

  /* raw process */

  def process_builder(cmd: JList[String],
    cwd: JFile = null,
    env: JMap[String, String] = settings(),
    redirect: Boolean = false): ProcessBuilder =
  {
    val builder = new ProcessBuilder

    // fragile on Windows:
    // see https://docs.microsoft.com/en-us/cpp/cpp/main-function-command-line-args?view=msvc-160
    builder.command(cmd)

    if (cwd != null) builder.directory(cwd)
    if (env != null) {
      builder.environment.clear()
      builder.environment().putAll(env)
    }
    builder.redirectErrorStream(redirect)
  }

  class Exec_Result(val rc: Int, val out: String, val err: String)
  {
    def ok: Boolean = rc == 0
  }

  def exec_process(command_line: JList[String],
    cwd: JFile = null,
    env: JMap[String, String] = settings(),
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

  @volatile private var _settings: JMap[String, String] = null

  def settings(): JMap[String, String] =
  {
    if (_settings == null) init("", "")  // unsynchronized check
    _settings
  }

  def init(isabelle_root: String, cygwin_root: String): Unit = synchronized
  {
    if (_settings == null) {
      val isabelle_root1 =
        bootstrap_directory(isabelle_root, "ISABELLE_ROOT", "isabelle.root", "Isabelle root")

      val cygwin_root1 =
        if (Platform.is_windows) {
          val root = bootstrap_directory(cygwin_root, "CYGWIN_ROOT", "cygwin.root", "Cygwin root")
          cygwin_init(isabelle_root1, root)
          _settings = JMap.of("CYGWIN_ROOT", root)
          root
        }
        else ""

      val env = new HashMap(System.getenv())
      def env_default(a: String, b: String): Unit = if (b != "") env.putIfAbsent(a, b)

      env_default("CYGWIN_ROOT", cygwin_root1)
      env_default("TEMP_WINDOWS",
        {
          val temp = if (Platform.is_windows) System.getenv("TEMP") else null
          if (temp != null && temp.contains('\\')) temp else ""
        })
      env_default("ISABELLE_JDK_HOME", File.standard_path(jdk_home()))
      env_default("HOME", System.getProperty("user.home", ""))
      env_default("ISABELLE_APP", System.getProperty("isabelle.app", ""))

      val settings = new HashMap[String, String]
      val settings_file = Files.createTempFile(null, null)
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
        cmd.add(settings_file.toString)

        val res = exec_process(cmd, env = env, redirect = true)
        if (!res.ok) error(res.out)

        for (s <- space_explode('\u0000', Files.readString(settings_file))) {
          val i = s.indexOf('=')
          if (i > 0) settings.put(s.substring(0, i), s.substring(i + 1))
          else if (i < 0 && s.nonEmpty) settings.put(s, "")
        }
      }
      finally { Files.delete(settings_file) }

      if (Platform.is_windows) settings.put("CYGWIN_ROOT", cygwin_root1)

      settings.put("PATH", settings.get("PATH_JVM"))
      settings.remove("PATH_JVM")

      _settings = JMap.copyOf(settings)
    }
  }
}
