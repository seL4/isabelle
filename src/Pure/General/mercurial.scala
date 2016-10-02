/*  Title:      Pure/General/mercurial.scala
    Author:     Makarius

Support for Mercurial repositories.
*/

package isabelle


import java.io.{File => JFile}


object Mercurial
{
  /* command-line syntax */

  def opt_rev(rev: String): String = if (rev == "") "" else " --rev " + File.bash_string(rev)


  /* repository access */

  def open_repository(root: Path): Repository = new Repository(root)

  class Repository private[Mercurial](val root: Path)
  {
    override def toString: String = root.toString

    def close() { }

    def command(cmd: String, cwd: JFile = null): Process_Result =
      Isabelle_System.hg("--repository " + File.bash_path(root) + " " + cmd, cwd = cwd)

    def identify(rev: String = "", options: String = ""): String =
      command("id -i " + options + opt_rev(rev)).check.out_lines.headOption getOrElse ""

    def manifest(rev: String = "", options: String = ""): List[String] =
      command("manifest " + options + opt_rev(rev)).check.out_lines

    command("root").check
  }
}
