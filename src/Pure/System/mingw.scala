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

  def standard_path(path: Path): String =
    root match {
      case Some(msys_root) if Platform.is_windows =>
        val command_line =
          java.util.List.of(
            File.platform_path(msys_root) + "\\usr\\bin\\cygpath", "-u", File.platform_path(path))
        val res = isabelle.setup.Environment.exec_process(command_line, null, null, false)
        if (res.ok) Library.trim_line(res.out)
        else error("Error: " + quote(Library.trim_line(res.err)))
      case _ => File.standard_path(path)
    }

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
