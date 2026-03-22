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


  /* support for platform-specific execution */

  object Bash_Context {
    def apply(
      ssh: SSH.System = SSH.Local,
      mingw_root: Option[Path] = None,
      apple: Boolean = true,
      progress: Progress = new Progress
    ): Bash_Context = {
      val context_ssh = ssh
      val context_platform =
        ssh.ssh_session match {
          case None => local
          case Some(session) => remote(session)
        }
      val context_mingw =
        mingw_root match {
          case None => MinGW.none
          case Some(root) => MinGW.init(root = root, ssh = ssh)
        }
      val context_apple = apple
      val context_progress = progress
      new Bash_Context {
        override def ssh: SSH.System = context_ssh
        override def isabelle_platform: Isabelle_Platform = context_platform
        override def mingw: MinGW = context_mingw
        override def apple: Boolean = context_apple
        override def progress: Progress = context_progress
      }
    }
  }

  trait Bash_Context {
    def ssh: SSH.System
    def isabelle_platform: Isabelle_Platform
    def mingw: MinGW
    def apple: Boolean
    def progress: Progress

    def ISABELLE_PLATFORM: String = isabelle_platform.ISABELLE_PLATFORM(windows = true, apple = apple)
    override def toString: String = ISABELLE_PLATFORM

    def is_linux_arm: Boolean = isabelle_platform.is_linux && isabelle_platform.is_arm
    def is_macos_arm: Boolean = isabelle_platform.is_macos && isabelle_platform.is_arm && apple
    def is_arm: Boolean = is_linux_arm || is_macos_arm

    def standard_path(path: Path): String =
      mingw.standard_path(File.platform_path(path))

    // bash without bash_process wrapper
    def bash(script: String,
      cwd: Path = Path.current,
      env: JMap[String, String] = Isabelle_System.Settings.env(),
    ): Process_Result = {
      progress.bash(
        if (is_macos_arm) "arch -arch arm64 bash -c " + Bash.string(script)
        else mingw.bash_script(script),
        ssh = ssh, cwd = cwd, env = env, echo = progress.verbose)
    }

    def library_path: (String, String) = {
      val x =
        if (isabelle_platform.is_linux) "LD_LIBRARY_PATH"
        else if (isabelle_platform.is_macos) "DYLD_LIBRARY_PATH"
        else if (isabelle_platform.is_windows) "PATH"
        else error("Bad platform " + ISABELLE_PLATFORM)
      val y =
        if (isabelle_platform.is_linux || isabelle_platform.is_macos) "lib"
        else if (isabelle_platform.is_windows) "bin"
        else error("Bad platform " + ISABELLE_PLATFORM)
      (x, y)
    }

    def library_closure(path: Path,
      env_prefix: String = "",
      filter: String => Boolean = _ => true
    ): List[String] = {
      val exe_path = path.expand
      val exe_dir = exe_path.dir
      val exe = exe_path.base

      val lines = {
        val ldd = if (isabelle_platform.is_macos) "otool -L" else "ldd"
        val script = mingw.bash_script(env_prefix + ldd + " " + ssh.bash_path(exe))
        split_lines(bash(script, cwd = exe_dir).check.out)
      }

      def lib_name(lib: String): String =
        Library.take_prefix[Char](c => c != '.' && c != '-',
          Library.take_suffix[Char](_ != '/', lib.toList)._2)._1.mkString

      val libs =
        if (isabelle_platform.is_macos) {
          val Pattern = """^\s*(/.+)\s+\(.*\)$""".r
          for {
            case Pattern(lib) <- lines
            if !lib.startsWith("@executable_path/") && filter(lib_name(lib))
          } yield lib
        }
        else {
          val Pattern = """^.*=>\s*(/.+)\s+\(.*\)$""".r
          for { case Pattern(lib) <- lines if filter(lib_name(lib)) }
            yield ssh.standard_path(mingw.platform_path(lib))
        }

      if (libs.nonEmpty) {
        libs.foreach(lib => ssh.copy_file(Path.explode(lib), exe_dir))

        if (isabelle_platform.is_linux) {
          ssh.require_command("patchelf")
          bash("patchelf --force-rpath --set-rpath '$ORIGIN' " + ssh.bash_path(exe_path)).check
        }
        else if (isabelle_platform.is_macos) {
          val script =
            ("install_name_tool" ::
              libs.map(file => "-change " + Bash.string(file) + " " +
                Bash.string("@executable_path/" + Path.explode(file).file_name) + " " +
                ssh.bash_path(exe))).mkString(" ")
          bash(script, cwd = exe_dir).check
        }
      }

      libs
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
