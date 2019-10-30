/*  Title:      Pure/System/linux.scala
    Author:     Makarius

Specific support for Linux, notably Ubuntu/Debian.
*/

package isabelle


import scala.util.matching.Regex


object Linux
{
  /* check system */

  def check_system(): Unit =
    if (!Platform.is_linux) error("Not a Linux system")

  def check_system_root(): Unit =
  {
    check_system()
    if (Isabelle_System.bash("id -u").check.out != "0") error("Not running as superuser (root)")
  }


  /* release */

  object Release
  {
    private val ID = """^Distributor ID:\s*(\S.*)$""".r
    private val RELEASE = """^Release:\s*(\S.*)$""".r
    private val DESCRIPTION = """^Description:\s*(\S.*)$""".r

    def apply(): Release =
    {
      val lines = Isabelle_System.bash("lsb_release -a").check.out_lines
      def find(R: Regex): String = lines.collectFirst({ case R(a) => a }).getOrElse("Unknown")
      new Release(find(ID), find(RELEASE), find(DESCRIPTION))
    }
  }

  final class Release private(val id: String, val release: String, val description: String)
  {
    override def toString: String = description

    def is_ubuntu: Boolean = id == "Ubuntu"
  }


  /* packages */

  def reboot_required(): Boolean =
    Path.explode("/var/run/reboot-required").is_file

  def check_reboot_required(): Unit =
    if (reboot_required()) error("Reboot required")

  def package_update(progress: Progress = No_Progress): Unit =
    progress.bash(
      """apt-get update -y && apt-get upgrade -y && apt autoremove -y""",
      echo = true).check

  def package_install(packages: List[String], progress: Progress = No_Progress): Unit =
    progress.bash("apt-get install -y -- " + Bash.strings(packages), echo = true).check
}
