/*  Title:      Pure/System/executable.scala
    Author:     Makarius

Support for platform-specific executables.
*/

package isabelle


object Executable
{
  def libraries_closure(path: Path,
    mingw: MinGW = MinGW.none,
    filter: String => Boolean = _ => true,
    patchelf: Boolean = false): List[String] =
  {
    val exe_path = path.expand
    val exe_dir = exe_path.dir
    val exe = exe_path.base

    val ldd_lines =
    {
      val ldd = if (Platform.is_macos) "otool -L" else "ldd"
      val script = mingw.bash_script(ldd + " " + File.bash_path(exe))
      Library.split_lines(Isabelle_System.bash(script, cwd = exe_dir.file).check.out)
    }

    def lib_name(lib: String): String =
      Library.take_prefix[Char](c => c != '.' && c != '-',
        Library.take_suffix[Char](_ != '/', lib.toList)._2)._1.mkString

    val libs =
      if (Platform.is_macos) {
        val Pattern = """^\s*(/.+)\s+\(.*\)$""".r
        for {
          Pattern(lib) <- ldd_lines
          if !lib.startsWith("@executable_path/") && filter(lib_name(lib))
        } yield lib
      }
      else {
        val Pattern = """^.*=>\s*(/.+)\s+\(.*\)$""".r
        val prefix =
          mingw.root match {
            case None => ""
            case Some(path) => path.absolute.implode
          }
        for { Pattern(lib) <- ldd_lines if filter(lib_name(lib)) }
          yield prefix + lib
      }

    if (libs.nonEmpty) {
      libs.foreach(lib => Isabelle_System.copy_file(Path.explode(lib), exe_dir))

      if (Platform.is_linux) {
        if (patchelf) {
          // requires e.g. Ubuntu 16.04 LTS
          Isabelle_System.require_command("patchelf")
          Isabelle_System.bash("patchelf --force-rpath --set-rpath '$ORIGIN' " + File.bash_path(exe_path)).check
        }
        else {
          // requires e.g. LDFLAGS=-Wl,-rpath,_DUMMY_
          Isabelle_System.require_command("chrpath")
          Isabelle_System.bash("chrpath -r '$ORIGIN' " + File.bash_path(exe_path)).check
        }
      }
      else if (Platform.is_macos) {
        val script =
          ("install_name_tool" ::
            libs.map(file => "-change " + Bash.string(file) + " " +
              Bash.string("@executable_path/" + Path.explode(file).file_name) + " " +
              File.bash_path(exe))).mkString(" ")
        Isabelle_System.bash(script, cwd = exe_dir.file).check
      }
    }

    libs
  }
}
