/*  Title:      Pure/System/isabelle_tool.scala
    Author:     Makarius

Isabelle system tools: external executables or internal Scala functions.
*/

package isabelle


object Isabelle_Tool
{
  /* external tools */

  private def dirs(): List[Path] = Path.split(Isabelle_System.getenv_strict("ISABELLE_TOOLS"))

  private def is_external(dir: Path, name: String): Boolean =
  {
    val file = (dir + Path.basic(name)).file
    try {
      file.isFile && file.canRead && file.canExecute &&
        !name.endsWith("~") && !name.endsWith(".orig")
    }
    catch { case _: SecurityException => false }
  }

  private def run_external(dir: Path, name: String)(args: List[String]): Nothing =
  {
    val tool = dir + Path.basic(name)
    val result = Isabelle_System.bash(File.bash_path(tool) + " " + File.bash_args(args))
    sys.exit(result.print_stdout.rc)
  }

  private def find_external(name: String): Option[List[String] => Unit] =
    dirs.collectFirst({ case dir if is_external(dir, name) => run_external(dir, name) })


  /* command line entry point */

  private def tool_descriptions(): List[String] =
  {
    val Description = """.*\bDESCRIPTION: *(.*)""".r
    val entries =
      for {
        dir <- dirs() if dir.is_dir
        name <- File.read_dir(dir) if is_external(dir, name)
      } yield {
        val source = File.read(dir + Path.basic(name))
        split_lines(source).collectFirst({ case Description(s) => s }) match {
          case None => (name, "")
          case Some(description) => (name, " - " + description)
        }
      }
    entries.sortBy(_._1).map({ case (a, b) => a + b })
  }

  def main(args: Array[String])
  {
    Command_Line.tool0 {
      args.toList match {
        case Nil | List("-?") =>
          Getopts("""
Usage: isabelle TOOL [ARGS ...]

  Start Isabelle TOOL with ARGS; pass "-?" for tool-specific help.

Available tools:""" + tool_descriptions.mkString("\n  ", "\n  ", "\n")).usage
        case tool_name :: tool_args =>
          find_external(tool_name) match {
            case Some(run) => run(tool_args)
            case None => error("Unknown Isabelle tool: " + quote(tool_name))
          }
      }
    }
  }
}
