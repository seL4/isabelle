/*  Title:      Pure/System/isabelle_env.scala
    Author:     Makarius

Fundamental Isabelle system environment: quasi-static module with
optional init operation.
*/

package isabelle.setup


import java.util.Locale
import java.util.regex.Pattern
import java.util.{HashMap, LinkedList, List => JList, Map => JMap}
import java.io.{File => JFile}
import java.nio.file.Files


object Isabelle_Env
{
  val is_windows: Boolean = System.getProperty("os.name", "").startsWith("Windows")

  def runtime_exception(message: String): Nothing = throw new RuntimeException(message)

  def quote(s: String): String = "\"" + s + "\""



  /** bootstrap information **/

  def bootstrap_directory(
    preference: String, variable: String, property: String, description: String): String =
  {
    val a = preference  // explicit argument
    val b = System.getenv(variable)  // e.g. inherited from running isabelle tool
    val c = System.getProperty(property)  // e.g. via JVM application boot process
    val dir =
      if (a != null && a.nonEmpty) a
      else if (b != null && b.nonEmpty) b
      else if (c != null && c.nonEmpty) c
      else runtime_exception("Unknown " + description + " directory")

    if ((new JFile(dir)).isDirectory) dir
    else runtime_exception("Bad " + description + " directory " + quote(dir))
  }



  /** Support for Cygwin as POSIX emulation on Windows **/

  /* system path representations */

  def standard_path(cygwin_root: String, platform_path: String): String =
    if (is_windows) {
      val backslashes = platform_path.replace('/', '\\')
      def slashes(s: String): String = s.replace('\\', '/')

      val root_pattern = Pattern.compile("(?i)" + Pattern.quote(cygwin_root) + """(?:\\+|\z)(.*)""")
      val root_matcher = root_pattern.matcher(backslashes)

      val drive_pattern = Pattern.compile("""([a-zA-Z]):\\*(.*)""")
      val drive_matcher = drive_pattern.matcher(backslashes)

      if (root_matcher.matches) {
        val rest = root_matcher.group(1)
        "/" + slashes(rest)
      }
      else if (drive_matcher.matches) {
        val letter = drive_matcher.group(1).toLowerCase(Locale.ROOT)
        val rest = drive_matcher.group(2)
        "/cygdrive/" + letter + (if (rest == "") "" else "/" + slashes(rest))
      }
      else slashes(backslashes)
    }
    else platform_path

  def platform_path(cygwin_root: String, standard_path: String): String =
    if (is_windows) {
      val result_path = new StringBuilder

      val cygdrive_pattern = Pattern.compile("/cygdrive/([a-zA-Z])($|/.*)")
      val cygdrive_matcher = cygdrive_pattern.matcher(standard_path)

      val named_root_pattern = Pattern.compile("//+([^/]*)(.*)")
      val named_root_matcher = named_root_pattern.matcher(standard_path)

      val rest =
        if (cygdrive_matcher.matches) {
          val drive = cygdrive_matcher.group(1).toUpperCase(Locale.ROOT)
          val rest = cygdrive_matcher.group(2)
          result_path ++= drive
          result_path ++= ":"
          result_path ++= JFile.separator
          rest
        }
        else if (named_root_matcher.matches) {
          val root = named_root_matcher.group(1)
          val rest = named_root_matcher.group(2)
          result_path ++= JFile.separator
          result_path ++= JFile.separator
          result_path ++= root
          rest
        }
        else {
          if (standard_path.startsWith("/")) result_path ++= cygwin_root
          standard_path
        }
      for (p <- rest.split("/", -1) if p != "") {
        val len = result_path.length
        if (len > 0 && result_path(len - 1) != JFile.separatorChar)
          result_path += JFile.separatorChar
        result_path ++= p
      }
      result_path.toString
    }
    else standard_path


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
    if (is_windows) {
      def cygwin_exec(cmd: JList[String]): Unit =
      {
        val cwd = new JFile(isabelle_root)
        val env = new HashMap(System.getenv())
        env.put("CYGWIN", "nodosfilewarning")
        val res = exec_process(cmd, cwd = cwd, env = env, redirect = true)
        if (!res.ok) runtime_exception(res.out)
      }

      val uninitialized_file = new JFile(cygwin_root, "isabelle\\uninitialized")
      val uninitialized = uninitialized_file.isFile && uninitialized_file.delete

      if (uninitialized) {
        val symlinks_path = (new JFile(cygwin_root + "\\isabelle\\symlinks")).toPath
        val symlinks = Files.readAllLines(symlinks_path).toArray(new Array[String](0))

        // recover symlinks
        var i = 0
        val m = symlinks.length
        val n = if (m > 0 && symlinks(m - 1).isEmpty) m - 1 else m
        while (i < n) {
          if (i + 1 < n) {
            val target = symlinks(i)
            val content = symlinks(i + 1)
            cygwin_link(content, new JFile(isabelle_root, target))
            i += 2
          }
          else runtime_exception("Unbalanced symlinks list")
        }

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

  def init(_isabelle_root: String, _cygwin_root: String): Unit = synchronized
  {
    if (_settings == null) {
      val isabelle_root =
        bootstrap_directory(_isabelle_root, "ISABELLE_ROOT", "isabelle.root", "Isabelle root")

      val cygwin_root =
        if (is_windows) {
          val root = bootstrap_directory(_cygwin_root, "CYGWIN_ROOT", "cygwin.root", "Cygwin root")
          cygwin_init(isabelle_root, root)
          root
        }
        else ""

      val env = new HashMap(System.getenv())
      def env_default(a: String, b: String): Unit = if (b != "") env.putIfAbsent(a, b)

      env_default("CYGWIN_ROOT", cygwin_root)
      env_default("TEMP_WINDOWS",
        {
          val temp = if (is_windows) System.getenv("TEMP") else null
          if (temp != null && temp.contains('\\')) temp else ""
        })
      env_default("ISABELLE_JDK_HOME",
        standard_path(cygwin_root, System.getProperty("java.home", "")))
      env_default("HOME", System.getProperty("user.home", ""))
      env_default("ISABELLE_APP", System.getProperty("isabelle.app", ""))

      val settings = new HashMap[String, String]
      val settings_file = Files.createTempFile(null, null)
      try {
        val cmd = new LinkedList[String]
        if (is_windows) {
          cmd.add(cygwin_root + "\\bin\\bash")
          cmd.add("-l")
          cmd.add(standard_path(cygwin_root, isabelle_root + "\\bin\\isabelle"))
        } else {
          cmd.add(isabelle_root + "/bin/isabelle")
        }
        cmd.add("getenv")
        cmd.add("-d")
        cmd.add(settings_file.toString)

        val res = exec_process(cmd, env = env, redirect = true)
        if (!res.ok) runtime_exception(res.out)

        for (s <- Files.readString(settings_file).split("\u0000", -1)) {
          val i = s.indexOf('=')
          if (i > 0) settings.put(s.substring(0, i), s.substring(i + 1))
          else if (i < 0 && s.nonEmpty) settings.put(s, "")
        }
      }
      finally { Files.delete(settings_file) }

      if (is_windows) settings.put("CYGWIN_ROOT", cygwin_root)

      settings.put("PATH", settings.get("PATH_JVM"))
      settings.remove("PATH_JVM")

      _settings = JMap.copyOf(settings)
    }
  }
}
