/*  Title:      Pure/System/mingw.scala
    Author:     Makarius

Support for MSYS2/MinGW64 on Windows.
*/

package isabelle


object MinGW {
  def default_env_prefix: String =
    Bash.exports(
      "PATH=/ucrt64/bin:/usr/local/bin:/usr/bin:/bin",
      "CONFIG_SITE=/etc/config.site",
      "MSYSTEM=UCRT64") + "source /etc/msystem\n"

  val default_root: Path = Path.explode("/cygdrive/c/msys64")

  def apply(root: Option[Path] = Some(default_root), ssh: SSH.System = SSH.Local) =
    new MinGW(root, ssh)

  val none: MinGW = apply(root = None)
}

class MinGW private(val root: Option[Path], ssh: SSH.System) {
  override def toString: String = {
    val a = if_proper(root, "root = " + root.get)
    val b = if_proper(!ssh.is_local, "ssh = " + ssh.toString)
    if (a.isEmpty && b.isEmpty) "MinGW.none"
    else "MinGW(" + a + if_proper(a.nonEmpty && b.nonEmpty, ", ") + b + ")"
  }

  private def is_windows: Boolean = ssh.isabelle_platform.is_windows

  private def convert_path(str: String, opt: String): Option[String] =
    root match {
      case Some(msys_root) if is_windows =>
        val cmd = msys_root + Path.explode("usr/bin/cygpath")
        if (ssh.is_local) {
          val command_line = java.util.List.of(ssh.platform_path(cmd), opt, str)
          val res = isabelle.setup.Environment.exec_process(command_line, null, null, false)
          if (res.ok) Some(Library.trim_line(res.out))
          else error("Error: " + quote(Library.trim_line(res.err)))
        }
        else {
          val res = ssh.execute(ssh.bash_path(cmd) + " " + Bash.strings(List(opt, str)))
          if (res.ok) Some(Library.trim_line(res.out))
          else error("Error: " + quote(Library.trim_line(res.err)))
       }
      case _ => None
    }

  def standard_path(platform_path: String): String =
    convert_path(platform_path, "-u") getOrElse ssh.standard_path(platform_path)

  def platform_path(standard_path: String): String =
    convert_path(standard_path, "-w") getOrElse ssh.platform_path(standard_path)

  def bash_script(script: String, env_prefix: String = MinGW.default_env_prefix): String =
    root match {
      case Some(msys_root) if is_windows =>
        ssh.bash_path(msys_root + Path.explode("usr/bin/bash")) +
          " -c " + Bash.string(env_prefix + script)
      case _ => script
    }

  def get_root: Path =
    if (!is_windows) error("Windows platform required")
    else if (root.isEmpty) error("Windows platform requires msys/mingw root specification")
    else root.get

  def check(): Unit = {
    if (is_windows) {
      get_root
      try { require(ssh.execute(bash_script("uname -s")).check.out.startsWith("MSYS")) }
      catch { case ERROR(msg) => cat_error("Bad msys/mingw installation " + get_root, msg) }
    }
  }
}
