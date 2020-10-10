/*  Title:      Pure/System/mingw.scala
    Author:     Makarius

Support for MSYS2/MinGW64 on Windows.
*/

package isabelle


object MinGW
{
  val none: Context = new Context(None)
  def context(root: Path) = new Context(Some(root))

  def environment: List[(String, String)] =
    List("PATH" -> "/usr/bin:/bin:/mingw64/bin", "CONFIG_SITE" -> "/mingw64/etc/config.site")

  def environment_prefix: String =
    (for ((a, b) <- environment) yield Bash.string(a) + "=" + Bash.string(b))
      .mkString("/usr/bin/env ", " ", " ")

  class Context private[MinGW](val root: Option[Path])
  {
    override def toString: String =
      root match {
        case None => "MinGW.none"
        case Some(msys_root) => "MinGW.context(" + msys_root.toString + ")"
      }

    def bash_command(command: String): String =
      root match {
        case None => command
        case Some(msys_root) =>
          File.bash_path(msys_root + Path.explode("usr/bin/bash")) +
            " -c " + Bash.string(environment_prefix + command)
      }

    def get_root: Path =
      if (!Platform.is_windows) error("Windows platform required")
      else if (root.isEmpty) error("Windows platform needs specification of msys root directory")
      else root.get

    def check
    {
      if (Platform.is_windows) {
        get_root
        val result = Isabelle_System.bash(bash_command("uname -s")).check
        if (!result.out.startsWith("MSYS")) error("Bad msys installation " + get_root)
      }
    }
  }
}
