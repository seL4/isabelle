/*  Title:      Pure/System/executable.scala
    Author:     Makarius

Support for platform-specific executables.
*/

package isabelle


object Executable
{
  def libraries(path: Path, mingw: MinGW = MinGW.none): List[Path] =
  {
    val path1 = path.expand
    val dir = path1.dir
    val exe = path1.base

    def command_output(cmd: String): List[String] =
    {
      val script = mingw.bash_script(cmd + " " + File.bash_path(exe))
      Library.split_lines(Isabelle_System.bash(script, cwd = dir.file).check.out)
    }

    if (Platform.is_macos) {
      val Pattern = """^\s*(.+)\s+\(.*\)$""".r
      for { Pattern(a) <- command_output("otool -L") } yield {
        Library.try_unprefix("@executable_path/", a) match {
          case None => Path.explode(a)
          case Some(b) => dir + Path.explode(b)
        }
      }
    }
    else {
      val Pattern = """^.*=>\s*(.+)\s+\(.*\)$""".r
      for { Pattern(a) <- command_output("ldd") } yield Path.explode(a)
    }
  }
}
