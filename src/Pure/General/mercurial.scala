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

    def manifest(rev: String = "", cwd: JFile = null): List[String] =
      command("manifest" + opt_rev(rev), cwd = cwd).check.out_lines

    command("root").check
  }
}
