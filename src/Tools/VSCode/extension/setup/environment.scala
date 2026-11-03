/*  Title:      Tools/VSCode/extension/setup/environment.scala
    Author:     Fabian Huch

Isabelle system environment within node.js.
*/

package isabelle.setup

import scala.language.unsafeNulls

import scala.collection.mutable
import scala.jdk.CollectionConverters._
import scala.scalajs.js

import java.util.Locale
import java.util.regex.Pattern


object Environment {
  @js.native
  @js.annotation.JSGlobal("process")
  private object Process extends js.Object {
    val platform: String = js.native
    val env: js.Dictionary[String] = js.native
  }

  def is_windows(): Boolean = Process.platform == "win32"
  def is_linux(): Boolean = Process.platform == "linux"
  def is_macos(): Boolean = Process.platform == "darwin"


  /* system path representations */

  def slashes(s: String): String = s.replace('\\', '/')

  private val separator_char = if (is_windows()) '\\' else '/'

  def standard_path(cygwin_root: String, platform_path: String): String =
    if (is_windows()) {
      val backslashes = platform_path.replace('/', '\\')

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

  private class Expand_Platform_Path(cygwin_root: String) {
    val _result = new StringBuilder

    def result: String = _result.toString()

    def clear(): Unit = { _result.setLength(0) }
    def add(c: Char): Unit = { _result.append(c) }
    def add(s: String): Unit = { _result.append(s) }
    def separator(): Unit = {
      val n = _result.length()
      if (n > 0 && _result.charAt(n - 1) != separator_char) add(separator_char)
    }

    def check_root(standard_path: String): String = {
      var rest = standard_path
      val is_root = standard_path.startsWith("/")

      if (is_windows()) {
        val cygdrive_pattern = Pattern.compile("/cygdrive/([a-zA-Z])($|/.*)")
        val cygdrive_matcher = cygdrive_pattern.matcher(standard_path)

        val named_root_pattern = Pattern.compile("//+([^/]*)(.*)")
        val named_root_matcher = named_root_pattern.matcher(standard_path)

        if (cygdrive_matcher.matches()) {
          val drive = cygdrive_matcher.group(1).toUpperCase(Locale.ROOT)
          rest = cygdrive_matcher.group(2)
          clear()
          add(drive)
          add(':')
          add(separator_char)
        }
        else if (named_root_matcher.matches()) {
          val root = named_root_matcher.group(1)
          rest = named_root_matcher.group(2)
          clear()
          add(separator_char)
          add(separator_char)
          add(root)
        }
        else if (is_root) {
          clear()
          add(cygwin_root)
        }
      }
      else if (is_root) {
        clear()
        add(separator_char)
      }
      rest
    }

    def check_rest(env: java.util.Map[String, String], main: String): Unit = {
      for (p <- main.split("/", -1)) {
        if (env != null && p.startsWith("$")) {
          val v = p.substring(1)
          val res = env.getOrDefault(v, "")
          if (res.isEmpty) {
            throw new RuntimeException("Bad Isabelle environment variable: " + Library.quote(v))
          }
          else check(null, res)
        }
        else if (p.nonEmpty) {
          separator()
          add(p)
        }
      }
    }

    def check(env: java.util.Map[String, String], path: String): Unit =
      check_rest(env, check_root(path))
  }

  def expand_platform_path(
    env: java.util.Map[String, String],
    cygwin_root: String,
    standard_Path: String
  ): String = {
    val expand = new Expand_Platform_Path(cygwin_root)
    expand.check(env, standard_Path)
    expand.result
  }


  /* init (e.g. after extraction via 7zip) */

  def cygwin_init(isabelle_root: String, cygwin_root: String): Unit = { }


  /* implicit settings environment */

  private val _settings: mutable.Map[String, String] = Process.env

  def settings(): java.util.Map[String, String] = _settings.asJava

  def getenv(name: String): String = settings().getOrDefault(name, "")

  def init(_isabelle_root: String, _cygwin_root: String): Unit = { }


  /* Cygwin root (after init) */

  def cygwin_root(): String = getenv("CYGWIN_ROOT")

  def standard_path(platform_path: String): String = standard_path(cygwin_root(), platform_path)

  def expand_platform_path(standard_path: String): String =
    expand_platform_path(settings(), cygwin_root(), standard_path)

  def platform_path(standard_path: String): String =
    expand_platform_path(null, cygwin_root(), standard_path)
}
