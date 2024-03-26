/*  Title:      Pure/System/isabelle_platform.scala
    Author:     Makarius

General hardware and operating system type for Isabelle system tools.
*/

package isabelle


object Isabelle_Platform {
  val settings: List[String] =
    List(
      "ISABELLE_PLATFORM_FAMILY",
      "ISABELLE_PLATFORM64",
      "ISABELLE_WINDOWS_PLATFORM32",
      "ISABELLE_WINDOWS_PLATFORM64",
      "ISABELLE_APPLE_PLATFORM64")

  def apply(ssh: Option[SSH.Session] = None): Isabelle_Platform = {
    ssh match {
      case None =>
        new Isabelle_Platform(settings.map(a => (a, Isabelle_System.getenv(a))))
      case Some(ssh) =>
        val script =
          File.read(Path.explode("~~/lib/scripts/isabelle-platform")) + "\n" +
            settings.map(a => "echo \"" + Bash.string(a) + "=$" + Bash.string(a) + "\"").mkString("\n")
        val result = ssh.execute("bash -c " + Bash.string(script)).check
        new Isabelle_Platform(
          result.out_lines.map(line =>
            Properties.Eq.unapply(line) getOrElse error("Bad output: " + quote(result.out))))
    }
  }

  lazy val self: Isabelle_Platform = apply()
}

class Isabelle_Platform private(val settings: List[(String, String)]) {
  private def get(name: String): String =
    settings.collectFirst({ case (a, b) if a == name => b }).
      getOrElse(error("Bad platform settings variable: " + quote(name)))

  val ISABELLE_PLATFORM64: String = get("ISABELLE_PLATFORM64")
  val ISABELLE_WINDOWS_PLATFORM64: String = get("ISABELLE_WINDOWS_PLATFORM64")
  val ISABELLE_APPLE_PLATFORM64: String = get("ISABELLE_APPLE_PLATFORM64")

  def ISABELLE_PLATFORM(windows: Boolean = false, apple: Boolean = false): String =
    proper_string(if_proper(windows, ISABELLE_WINDOWS_PLATFORM64)) orElse
    proper_string(if_proper(apple, ISABELLE_APPLE_PLATFORM64)) orElse
    proper_string(ISABELLE_PLATFORM64) getOrElse error("Missing ISABELLE_PLATFORM64")

  def is_arm: Boolean =
    ISABELLE_PLATFORM64.startsWith("arm64-") ||
    ISABELLE_APPLE_PLATFORM64.startsWith("arm64-")

  val ISABELLE_PLATFORM_FAMILY: String = {
    val family0 = get("ISABELLE_PLATFORM_FAMILY")
    if (family0 == "linux" && is_arm) "linux_arm" else family0
  }

  def is_linux: Boolean = ISABELLE_PLATFORM_FAMILY.startsWith("linux")
  def is_macos: Boolean = ISABELLE_PLATFORM_FAMILY.startsWith("macos")
  def is_windows: Boolean = ISABELLE_PLATFORM_FAMILY.startsWith("windows")

  def arch_64: String = if (is_arm) "arm64" else "x86_64"
  def arch_64_32: String = if (is_arm) "arm64_32" else "x86_64_32"

  def os_name: String = if (is_macos) "darwin" else if (is_windows) "windows" else "linux"

  override def toString: String = ISABELLE_PLATFORM_FAMILY
}
