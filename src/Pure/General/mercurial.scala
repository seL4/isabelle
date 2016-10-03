/*  Title:      Pure/General/mercurial.scala
    Author:     Makarius

Support for Mercurial repositories.
*/

package isabelle


import java.io.{File => JFile}


object Mercurial
{
  /* command-line syntax */

  def optional(s: String, prefix: String = ""): String =
    if (s == "") "" else " " + prefix + " " + File.bash_string(s)

  def opt_flag(flag: String, b: Boolean): String = if (b) " " + flag else ""
  def opt_rev(s: String): String = optional(s, "--rev")
  def opt_template(s: String): String = optional(s, "--template")


  /* repository access */

  def open_repository(root: Path): Repository = new Repository(root)

  class Repository private[Mercurial](val root: Path)
  {
    override def toString: String = root.toString

    def close() { }

    def command(cmd: String, cwd: JFile = null): Process_Result =
      Isabelle_System.hg("--repository " + File.bash_path(root) + " " + cmd, cwd = cwd)


    def heads(template: String = "{node|short}\n", options: String = ""): List[String] =
      command("heads " + options + opt_template(template)).check.out_lines

    def identify(rev: String = "", options: String = ""): String =
      command("id " + options + opt_rev(rev)).check.out_lines.headOption getOrElse ""

    def manifest(rev: String = "", options: String = ""): List[String] =
      command("manifest " + options + opt_rev(rev)).check.out_lines

    def log(rev: String = "", options: String = ""): String =
      Library.trim_line(command("log " + options + opt_rev(rev)).check.out)

    def pull(remote: String = "", rev: String = "", options: String = ""): Unit =
      command("pull " + options + opt_rev(rev) + optional(remote)).check

    def update(rev: String = "", clean: Boolean = false, check: Boolean = false, options: String = "")
    {
      command("update " + options +
        opt_rev(rev) + opt_flag("--clean", clean) + opt_flag("--check", check)).check
    }

    command("root").check
  }
}
