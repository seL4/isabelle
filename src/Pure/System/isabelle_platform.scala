/*  Title:      Pure/System/isabelle_platform.scala
    Author:     Makarius

General hardware and operating system type for Isabelle system tools.
*/

package isabelle


object Isabelle_Platform
{
  val settings: List[String] =
    List(
      "ISABELLE_PLATFORM_FAMILY",
      "ISABELLE_PLATFORM32",
      "ISABELLE_PLATFORM64",
      "ISABELLE_WINDOWS_PLATFORM32",
      "ISABELLE_WINDOWS_PLATFORM64")

  def local(): Isabelle_Platform =
    new Isabelle_Platform(settings.map(a => (a, Isabelle_System.getenv(a))))

  def remote(ssh: SSH.Session): Isabelle_Platform =
  {
    val script =
      File.read(Path.explode("~~/lib/scripts/isabelle-platform")) + "\n" +
      settings.map(a => "echo \"" + Bash.string(a) + "=$" + Bash.string(a) + "\"").mkString("\n")
    val result = ssh.execute("bash -c " + Bash.string(script)).check
    val values =
      result.out_lines.map(line =>
        space_explode('=', line) match {
          case List(a, b) => (a, b)
          case _ => error("Bad output: " + quote(result.out))
        })
    new Isabelle_Platform(values)
  }
}

class Isabelle_Platform private(values: List[(String, String)])
{
  private def get(name: String): String =
    values.collectFirst({ case (a, b) if a == name => b }).
      getOrElse(error("Bad platform settings variable: " + quote(name)))

  val ISABELLE_PLATFORM_FAMILY: String = get("ISABELLE_PLATFORM_FAMILY")
  val ISABELLE_PLATFORM32: String = get("ISABELLE_PLATFORM32")
  val ISABELLE_PLATFORM64: String = get("ISABELLE_PLATFORM64")
  val ISABELLE_WINDOWS_PLATFORM32: String = get("ISABELLE_WINDOWS_PLATFORM32")
  val ISABELLE_WINDOWS_PLATFORM64: String = get("ISABELLE_WINDOWS_PLATFORM64")

  val is_linux: Boolean = ISABELLE_PLATFORM_FAMILY == "linux"
  val is_macos: Boolean = ISABELLE_PLATFORM_FAMILY == "macos"
  val is_windows: Boolean = ISABELLE_PLATFORM_FAMILY == "windows"

  override def toString: String = ISABELLE_PLATFORM_FAMILY
}
