/*  Title:      Pure/System/isabelle_platform.scala
    Author:     Makarius

Isabelle/Scala platform information, based on settings environment.
*/

package isabelle


import java.util.{Map => JMap}


object Isabelle_Platform {
  val settings: List[String] =
    List(
      "ISABELLE_PLATFORM_FAMILY",
      "ISABELLE_PLATFORM64",
      "ISABELLE_WINDOWS_PLATFORM32",
      "ISABELLE_WINDOWS_PLATFORM64",
      "ISABELLE_APPLE_PLATFORM64")

  def make(env: Isabelle_System.Settings = Isabelle_System.Settings()): Isabelle_Platform =
    new Isabelle_Platform(settings.map(a => (a, Isabelle_System.getenv(a, env = env))))

  lazy val local: Isabelle_Platform = make()

  def remote(ssh: SSH.Session): Isabelle_Platform = {
    val script =
      File.read(Path.explode("~~/lib/scripts/isabelle-platform")) + "\n" +
        settings.map(a => "echo \"" + Bash.string(a) + "=$" + Bash.string(a) + "\"").mkString("\n")
    val result = ssh.execute("bash -c " + Bash.string(script)).check
    new Isabelle_Platform(
      result.out_lines.map(line =>
        Properties.Eq.unapply(line) getOrElse error("Bad output: " + quote(result.out))))
  }


  /* system context for progress/process */

  object Context {
    def apply(
      isabelle_platform: Isabelle_Platform = local,
      mingw: MinGW = MinGW.none,
      apple: Boolean = true,
      progress: Progress = new Progress
    ): Context = {
      val context_platform = isabelle_platform
      val context_mingw = mingw
      val context_apple = apple
      val context_progress = progress
      new Context {
        override def isabelle_platform: Isabelle_Platform = context_platform
        override def mingw: MinGW = context_mingw
        override def apple: Boolean = context_apple
        override def progress: Progress = context_progress
      }
    }
  }

  trait Context {
    def isabelle_platform: Isabelle_Platform
    def mingw: MinGW
    def apple: Boolean
    def progress: Progress

    def ISABELLE_PLATFORM: String = isabelle_platform.ISABELLE_PLATFORM(windows = true, apple = apple)
    def is_linux_arm: Boolean = isabelle_platform.is_linux && isabelle_platform.is_arm
    def is_macos_arm: Boolean = isabelle_platform.is_macos && isabelle_platform.is_arm && apple
    def is_arm: Boolean = is_linux_arm || is_macos_arm

    def standard_path(path: Path): String =
      mingw.standard_path(File.platform_path(path))

    def bash(script: String,
      cwd: Path = Path.current,
      env: JMap[String, String] = Isabelle_System.Settings.env(),
    ): Process_Result = {
      progress.bash(
        if (is_macos_arm) "arch -arch arm64 bash -c " + Bash.string(script)
        else mingw.bash_script(script),
        cwd = cwd, env = env, echo = progress.verbose)
    }
  }
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
