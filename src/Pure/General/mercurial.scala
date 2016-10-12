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

  def repository(root: Path, ssh: Option[SSH.Session] = None): Repository =
    new Repository(root, ssh)

  class Repository private[Mercurial](val root: Path, ssh: Option[SSH.Session])
  {
    hg =>

    override def toString: String =
      ssh match {
        case None => root.implode
        case Some(session) => quote(session.toString + ":" + root.implode)
      }

    def command(cmd: String): Process_Result =
    {
      val cmdline =
        "\"${HG:-hg}\" --repository " + File.bash_string(root.implode) + " --noninteractive " + cmd
      ssh match {
        case None => Isabelle_System.bash(cmdline)
        case Some(session) => session.execute(cmdline)
      }
    }

    def heads(template: String = "{node|short}\n", options: String = ""): List[String] =
      hg.command("heads " + options + opt_template(template)).check.out_lines

    def identify(rev: String = "", options: String = ""): String =
      hg.command("id " + options + opt_rev(rev)).check.out_lines.headOption getOrElse ""

    def manifest(rev: String = "", options: String = ""): List[String] =
      hg.command("manifest " + options + opt_rev(rev)).check.out_lines

    def log(rev: String = "", template: String = "", options: String = ""): String =
      hg.command("log " + options + opt_rev(rev) + opt_template(template)).check.out

    def pull(remote: String = "", rev: String = "", options: String = ""): Unit =
      hg.command("pull " + options + opt_rev(rev) + optional(remote)).check

    def update(rev: String = "", clean: Boolean = false, check: Boolean = false, options: String = "")
    {
      hg.command("update " + options +
        opt_rev(rev) + opt_flag("--clean", clean) + opt_flag("--check", check)).check
    }

    hg.command("root").check
  }
}
