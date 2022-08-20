/*  Title:      Pure/System/isabelle_tool.scala
    Author:     Makarius

Isabelle system tools: external executables or internal Scala functions.
*/

package isabelle


object Isabelle_Tool {
  /* external tools */

  private def dirs(): List[Path] = Path.split(Isabelle_System.getenv_strict("ISABELLE_TOOLS"))

  private def is_external(dir: Path, name: String): Boolean = {
    val file = (dir + Path.explode(name)).file
    try { file.isFile && file.canRead && file.canExecute && !File.is_backup(name) }
    catch { case _: SecurityException => false }
  }

  private def find_external(name: String): Option[List[String] => Unit] =
    dirs().collectFirst(
      {
        case dir if is_external(dir, name) =>
          { (args: List[String]) =>
            val tool = dir + Path.explode(name)
            val result = Isabelle_System.bash(File.bash_path(tool) + " " + Bash.strings(args))
            sys.exit(result.print_stdout.rc)
          }
      })


  /* internal tools */

  private lazy val internal_tools: List[Isabelle_Tool] =
    Isabelle_System.make_services(classOf[Isabelle_Scala_Tools]).flatMap(_.tools)

  private def find_internal(name: String): Option[List[String] => Unit] =
    internal_tools.collectFirst({
      case tool if tool.name == name =>
        args => Command_Line.tool { tool.body(args) }
      })


  /* list tools */

  abstract class Entry {
    def name: String
    def position: Properties.T
    def description: String
    def print: String =
      description match {
        case "" => name
        case descr => name + " - " + descr
      }
  }

  sealed case class External(name: String, path: Path) extends Entry {
    def position: Properties.T = Position.File(path.absolute.implode)
    def description: String = {
      val Pattern = """.*\bDESCRIPTION: *(.*)""".r
      split_lines(File.read(path)).collectFirst({ case Pattern(s) => s }) getOrElse ""
    }
  }

  def external_tools(): List[External] = {
    for {
      dir <- dirs() if dir.is_dir
      name <- File.read_dir(dir) if is_external(dir, name)
    } yield External(name, dir + Path.explode(name))
  }

  def isabelle_tools(): List[Entry] =
    (external_tools() ::: internal_tools).sortBy(_.name)

  object Isabelle_Tools extends Scala.Fun_String("isabelle_tools") {
    val here = Scala_Project.here
    def apply(arg: String): String =
      if (arg.nonEmpty) error("Bad argument: " + quote(arg))
      else {
        val result = isabelle_tools().map(entry => (entry.name, entry.position))
        val body = { import XML.Encode._; list(pair(string, properties))(result) }
        YXML.string_of_body(body)
      }
  }


  /* command line entry point */

  def main(args: Array[String]): Unit = {
    Command_Line.tool {
      args.toList match {
        case Nil | List("-?") =>
          val tool_descriptions = isabelle_tools().map(_.print)
          Getopts("""
Usage: isabelle TOOL [ARGS ...]

  Start Isabelle TOOL with ARGS; pass "-?" for tool-specific help.

Available tools:""" + tool_descriptions.mkString("\n  ", "\n  ", "\n")).usage()
        case tool_name :: tool_args =>
          find_external(tool_name) orElse find_internal(tool_name) match {
            case Some(tool) => tool(tool_args)
            case None => error("Unknown Isabelle tool: " + quote(tool_name))
          }
      }
    }
  }
}

sealed case class Isabelle_Tool(
  name: String,
  description: String,
  here: Scala_Project.Here,
  body: List[String] => Unit
) extends Isabelle_Tool.Entry {
  def position: Position.T = here.position
}

class Isabelle_Scala_Tools(val tools: Isabelle_Tool*) extends Isabelle_System.Service

class Tools extends Isabelle_Scala_Tools(
  Build.isabelle_tool,
  Build_Docker.isabelle_tool,
  Build_Job.isabelle_tool,
  CI_Build_Benchmark.isabelle_tool,
  Doc.isabelle_tool,
  Document_Build.isabelle_tool,
  Dump.isabelle_tool,
  Export.isabelle_tool,
  ML_Process.isabelle_tool,
  Mercurial.isabelle_tool1,
  Mercurial.isabelle_tool2,
  Mkroot.isabelle_tool,
  Logo.isabelle_tool,
  Options.isabelle_tool,
  Phabricator.isabelle_tool1,
  Phabricator.isabelle_tool2,
  Phabricator.isabelle_tool3,
  Phabricator.isabelle_tool4,
  Profiling_Report.isabelle_tool,
  Server.isabelle_tool,
  Sessions.isabelle_tool,
  Scala_Project.isabelle_tool,
  Sync.isabelle_tool,
  Update.isabelle_tool,
  Update_Cartouches.isabelle_tool,
  Update_Comments.isabelle_tool,
  Update_Header.isabelle_tool,
  Update_Then.isabelle_tool,
  Update_Theorems.isabelle_tool,
  isabelle.mirabelle.Mirabelle.isabelle_tool,
  isabelle.vscode.Language_Server.isabelle_tool,
  isabelle.vscode.VSCode_Main.isabelle_tool)

class Admin_Tools extends Isabelle_Scala_Tools(
  Build_CSDP.isabelle_tool,
  Build_Cygwin.isabelle_tool,
  Build_Doc.isabelle_tool,
  Build_E.isabelle_tool,
  Build_Fonts.isabelle_tool,
  Build_JCEF.isabelle_tool,
  Build_JDK.isabelle_tool,
  Build_JEdit.isabelle_tool,
  Build_Minisat.isabelle_tool,
  Build_PDFjs.isabelle_tool,
  Build_PolyML.isabelle_tool1,
  Build_PolyML.isabelle_tool2,
  Build_SPASS.isabelle_tool,
  Build_SQLite.isabelle_tool,
  Build_Scala.isabelle_tool,
  Build_Status.isabelle_tool,
  Build_Vampire.isabelle_tool,
  Build_VeriT.isabelle_tool,
  Build_Zipperposition.isabelle_tool,
  Check_Sources.isabelle_tool,
  Components.isabelle_tool,
  isabelle.vscode.Build_VSCode.isabelle_tool,
  isabelle.vscode.Build_VSCodium.isabelle_tool1,
  isabelle.vscode.Build_VSCodium.isabelle_tool2)
