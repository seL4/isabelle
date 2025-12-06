/*  Title:      Pure/System/executable.scala
    Author:     Makarius

Support for platform-specific executables.
*/

package isabelle


object Executable {
  def library_path(platform: Isabelle_Platform): (String, String) = {
    val x =
      if (platform.is_linux) "LD_LIBRARY_PATH"
      else if (platform.is_macos) "DYLD_LIBRARY_PATH"
      else if (platform.is_windows) "PATH"
      else error("Bad platform " + platform)
    val y =
      if (platform.is_linux || platform.is_macos) "lib"
      else if (platform.is_windows) "bin"
      else error("Bad platform " + platform)
    (x, y)
  }

  def library_closure(path: Path,
    env_prefix: String = "",
    mingw: MinGW = MinGW.none,
    filter: String => Boolean = _ => true
  ): List[String] = {
    val exe_path = path.expand
    val exe_dir = exe_path.dir
    val exe = exe_path.base

    val lines = {
      val ldd = if (Platform.is_macos) "otool -L" else "ldd"
      val script = mingw.bash_script(env_prefix + ldd + " " + File.bash_path(exe))
      split_lines(Isabelle_System.bash(script, cwd = exe_dir).check.out)
    }

    def lib_name(lib: String): String =
      Library.take_prefix[Char](c => c != '.' && c != '-',
        Library.take_suffix[Char](_ != '/', lib.toList)._2)._1.mkString

    val libs =
      if (Platform.is_macos) {
        val Pattern = """^\s*(/.+)\s+\(.*\)$""".r
        for {
          case Pattern(lib) <- lines
          if !lib.startsWith("@executable_path/") && filter(lib_name(lib))
        } yield lib
      }
      else {
        val Pattern = """^.*=>\s*(/.+)\s+\(.*\)$""".r
        for { case Pattern(lib) <- lines if filter(lib_name(lib)) }
          yield File.standard_path(mingw.platform_path(lib))
      }

    if (libs.nonEmpty) {
      libs.foreach(lib => Isabelle_System.copy_file(Path.explode(lib), exe_dir))

      if (Platform.is_linux) {
        Isabelle_System.require_command("patchelf")
        Isabelle_System.bash("patchelf --force-rpath --set-rpath '$ORIGIN' " + File.bash_path(exe_path)).check
      }
      else if (Platform.is_macos) {
        val script =
          ("install_name_tool" ::
            libs.map(file => "-change " + Bash.string(file) + " " +
              Bash.string("@executable_path/" + Path.explode(file).file_name) + " " +
              File.bash_path(exe))).mkString(" ")
        Isabelle_System.bash(script, cwd = exe_dir).check
      }
    }

    libs
  }
}
