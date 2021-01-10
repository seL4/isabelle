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
    def is_ubuntu_18_04: Boolean = is_ubuntu && release == "18.04"
    def is_ubuntu_20_04: Boolean = is_ubuntu && release == "20.04"
  }


  /* packages */

  def reboot_required(): Boolean =
    Path.explode("/var/run/reboot-required").is_file

  def check_reboot_required(): Unit =
    if (reboot_required()) error("Reboot required")

  def package_update(progress: Progress = new Progress): Unit =
    progress.bash(
      """apt-get update -y && apt-get upgrade -y && apt autoremove -y""",
      echo = true).check

  def package_install(packages: List[String], progress: Progress = new Progress): Unit =
    progress.bash("apt-get install -y -- " + Bash.strings(packages), echo = true).check

  def package_installed(name: String): Boolean =
  {
    val result = Isabelle_System.bash("dpkg-query -s " + Bash.string(name))
    val pattern = """^Status:.*installed.*$""".r.pattern
    result.ok && result.out_lines.exists(line => pattern.matcher(line).matches)
  }


  /* users */

  def user_exists(name: String): Boolean =
    Isabelle_System.bash("id " + Bash.string(name)).ok

  def user_entry(name: String, field: Int): String =
  {
    val result = Isabelle_System.bash("getent passwd " + Bash.string(name)).check
    val fields = space_explode(':', result.out)

    if (1 <= field && field <= fields.length) fields(field - 1)
    else error("No passwd field " + field + " for user " + quote(name))
  }

  def user_description(name: String): String = user_entry(name, 5).takeWhile(_ != ',')

  def user_home(name: String): String = user_entry(name, 6)

  def user_add(name: String,
    description: String = "",
    system: Boolean = false,
    ssh_setup: Boolean = false)
  {
    require(!description.contains(','), "malformed description")

    if (user_exists(name)) error("User already exists: " + quote(name))

    Isabelle_System.bash(
      "adduser --quiet --disabled-password --gecos " + Bash.string(description) +
        (if (system) " --system --group --shell /bin/bash " else "") +
        " " + Bash.string(name)).check

    if (ssh_setup) {
      val id_rsa = user_home(name) + "/.ssh/id_rsa"
      Isabelle_System.bash("""
if [ ! -f """ + Bash.string(id_rsa) + """ ]
then
  yes '\n' | sudo -i -u """ + Bash.string(name) +
    """ ssh-keygen -q -f """ + Bash.string(id_rsa) + """
fi
      """).check
    }
  }


  /* system services */

  def service_operation(op: String, name: String): Unit =
    Isabelle_System.bash("systemctl " + Bash.string(op) + " " + Bash.string(name)).check

  def service_enable(name: String) { service_operation("enable", name) }
  def service_disable(name: String) { service_operation("disable", name) }
  def service_start(name: String) { service_operation("start", name) }
  def service_stop(name: String) { service_operation("stop", name) }
  def service_restart(name: String) { service_operation("restart", name) }

  def service_shutdown(name: String)
  {
    try { service_stop(name) }
    catch { case ERROR(_) => }
  }

  def service_install(name: String, spec: String)
  {
    service_shutdown(name)

    val service_file = Path.explode("/lib/systemd/system") + Path.basic(name).ext("service")
    File.write(service_file, spec)
    Isabelle_System.chmod("644", service_file)

    service_enable(name)
    service_restart(name)
  }


  /* passwords */

  def generate_password(length: Int = 10): String =
  {
    require(length >= 6, "password too short")
    Isabelle_System.bash("pwgen " + length + " 1").check.out
  }
}
