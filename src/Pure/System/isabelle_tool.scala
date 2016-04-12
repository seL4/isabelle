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

  private def list_external(): List[(String, String)] =
  {
    val Description = """.*\bDESCRIPTION: *(.*)""".r
    for {
      dir <- dirs() if dir.is_dir
      name <- File.read_dir(dir) if is_external(dir, name)
    } yield {
      val source = File.read(dir + Path.basic(name))
      val description =
        split_lines(source).collectFirst({ case Description(s) => s }) getOrElse ""
      (name, description)
    }
  }

  private def find_external(name: String): Option[List[String] => Unit] =
    dirs.collectFirst({ case dir if is_external(dir, name) =>
      (args: List[String]) =>
        {
          val tool = dir + Path.basic(name)
          val result = Isabelle_System.bash(File.bash_path(tool) + " " + File.bash_args(args))
          sys.exit(result.print_stdout.rc)
        }
    })


  /* internal tools */

  private val internal_tools: List[Isabelle_Tool] =
    List(
      Build.isabelle_tool,
      Build_Doc.isabelle_tool,
      Check_Sources.isabelle_tool,
      Doc.isabelle_tool,
      ML_Process.isabelle_tool,
      Options.isabelle_tool,
      Update_Cartouches.isabelle_tool,
      Update_Header.isabelle_tool,
      Update_Then.isabelle_tool,
      Update_Theorems.isabelle_tool)

  private def list_internal(): List[(String, String)] =
    for (tool <- internal_tools.toList) yield (tool.name, tool.description)

  private def find_internal(name: String): Option[List[String] => Unit] =
    internal_tools.collectFirst({
      case tool if tool.name == name =>
        args => Command_Line.tool0 { tool.body(args) }
      })


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool0 {
      args.toList match {
        case Nil | List("-?") =>
          val tool_descriptions =
            (list_external() ::: list_internal()).sortBy(_._1).
              map({ case (a, "") => a case (a, b) => a + " - " + b })
          Getopts("""
Usage: isabelle TOOL [ARGS ...]

  Start Isabelle TOOL with ARGS; pass "-?" for tool-specific help.

Available tools:""" + tool_descriptions.mkString("\n  ", "\n  ", "\n")).usage
        case tool_name :: tool_args =>
          find_external(tool_name) orElse find_internal(tool_name) match {
            case Some(tool) => tool(tool_args)
            case None => error("Unknown Isabelle tool: " + quote(tool_name))
          }
      }
    }
  }
}

sealed case class Isabelle_Tool(name: String, description: String, body: List[String] => Unit)
