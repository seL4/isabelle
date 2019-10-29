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
}
