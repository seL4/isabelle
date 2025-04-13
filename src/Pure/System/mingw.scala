/*  Title:      Pure/System/mingw.scala
    Author:     Makarius

Support for MSYS2/MinGW64 on Windows.
*/

package isabelle


object MinGW {
  def env_prefix: String =
    Bash.exports("PATH=/usr/bin:/bin:/mingw64/bin", "CONFIG_SITE=/mingw64/etc/config.site")

  val none: MinGW = new MinGW(None)
  def apply(path: Path) = new MinGW(Some(path))
}

class MinGW private(val root: Option[Path]) {
  override def toString: String =
    root match {
      case None => "MinGW.none"
      case Some(msys_root) => "MinGW(" + msys_root.toString + ")"
    }

  private def convert_path(str: String, opt: String): Option[String] =
    root match {
      case Some(msys_root) if Platform.is_windows =>
        val command_line =
          java.util.List.of(
            File.platform_path(msys_root) + "\\usr\\bin\\cygpath", opt, str)
        val res = isabelle.setup.Environment.exec_process(command_line, null, null, false)
        if (res.ok) Some(Library.trim_line(res.out))
        else error("Error: " + quote(Library.trim_line(res.err)))
      case _ => None
    }

  def standard_path(platform_path: String): String =
    convert_path(platform_path, "-u") getOrElse File.standard_path(platform_path)

  def platform_path(standard_path: String): String =
    convert_path(standard_path, "-w") getOrElse File.platform_path(standard_path)

  def bash_script(script: String, env_prefix: String = MinGW.env_prefix): String =
    root match {
      case None => script
      case Some(msys_root) =>
        File.bash_path(msys_root + Path.explode("usr/bin/bash")) +
          " -c " + Bash.string(env_prefix + script)
    }

  def get_root: Path =
    if (!Platform.is_windows) error("Windows platform required")
    else if (root.isEmpty) error("Windows platform requires msys/mingw root specification")
    else root.get

  def check(): Unit = {
    if (Platform.is_windows) {
      get_root
      try { require(Isabelle_System.bash(bash_script("uname -s")).check.out.startsWith("MSYS")) }
      catch { case ERROR(msg) => cat_error("Bad msys/mingw installation " + get_root, msg) }
    }
  }
}
