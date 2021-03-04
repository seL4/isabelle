/*  Title:      Pure/System/isabelle_tool.scala
    Author:     Makarius
    Author:     Lars Hupel

Isabelle system tools: external executables or internal Scala functions.
*/

package isabelle

import java.net.URLClassLoader
import scala.reflect.runtime.universe
import scala.tools.reflect.{ToolBox, ToolBoxError}


object Isabelle_Tool
{
  /* Scala source tools */

  abstract class Body extends Function[List[String], Unit]

  private def compile(path: Path): Body =
  {
    def err(msg: String): Nothing =
      cat_error(msg, "The error(s) above occurred in Isabelle/Scala tool " + path)

    val source = File.read(path)

    val class_loader = new URLClassLoader(Array(), getClass.getClassLoader)
    val tool_box = universe.runtimeMirror(class_loader).mkToolBox()

    try {
      val symbol = tool_box.parse(source) match {
        case tree: universe.ModuleDef => tool_box.define(tree)
        case _ => err("Source does not describe a module (Scala object)")
      }
      tool_box.compile(universe.Ident(symbol))() match {
        case body: Body => body
        case _ => err("Ill-typed source: Isabelle_Tool.Body expected")
      }
    }
    catch {
      case e: ToolBoxError =>
        if (tool_box.frontEnd.hasErrors) {
          val infos = tool_box.frontEnd.infos.toList
          val msgs = infos.map(info => "Error in line " + info.pos.line + ":\n" + info.msg)
          err(msgs.mkString("\n"))
        }
        else
          err(e.toString)
    }
  }


  /* external tools */

  private def dirs(): List[Path] = Path.split(Isabelle_System.getenv_strict("ISABELLE_TOOLS"))

  private def is_external(dir: Path, file_name: String): Boolean =
  {
    val file = (dir + Path.explode(file_name)).file
    try {
      file.isFile && file.canRead &&
        (file_name.endsWith(".scala") || file.canExecute) &&
        !file_name.endsWith("~") && !file_name.endsWith(".orig")
    }
    catch { case _: SecurityException => false }
  }

  private def find_external(name: String): Option[List[String] => Unit] =
    dirs().collectFirst({
      case dir if is_external(dir, name + ".scala") =>
        compile(dir + Path.explode(name + ".scala"))
      case dir if is_external(dir, name) =>
        (args: List[String]) =>
          {
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

  abstract class Entry
  {
    def name: String
    def position: Properties.T
    def description: String
    def print: String =
      description match {
        case "" => name
        case descr => name + " - " + descr
      }
  }

  sealed case class External(name: String, path: Path) extends Entry
  {
    def position: Properties.T = Position.File(path.absolute.implode)
    def description: String =
    {
      val Pattern = """.*\bDESCRIPTION: *(.*)""".r
      split_lines(File.read(path)).collectFirst({ case Pattern(s) => s }) getOrElse ""
    }
  }

  def external_tools(): List[External] =
  {
    for {
      dir <- dirs() if dir.is_dir
      file_name <- File.read_dir(dir) if is_external(dir, file_name)
    } yield {
      val path = dir + Path.explode(file_name)
      val name = Library.perhaps_unsuffix(".scala", file_name)
      External(name, path)
    }
  }

  def isabelle_tools(): List[Entry] =
    (external_tools() ::: internal_tools).sortBy(_.name)

  object Isabelle_Tools extends Scala.Fun("isabelle_tools")
  {
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

  def main(args: Array[String]): Unit =
  {
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
  body: List[String] => Unit) extends Isabelle_Tool.Entry
{
  def position: Position.T = here.position
}

class Isabelle_Scala_Tools(val tools: Isabelle_Tool*) extends Isabelle_System.Service

class Tools extends Isabelle_Scala_Tools(
  Build.isabelle_tool,
  Build_Docker.isabelle_tool,
  Build_Job.isabelle_tool,
  Doc.isabelle_tool,
  Dump.isabelle_tool,
  Export.isabelle_tool,
  ML_Process.isabelle_tool,
  Mercurial.isabelle_tool,
  Mkroot.isabelle_tool,
  Options.isabelle_tool,
  Phabricator.isabelle_tool1,
  Phabricator.isabelle_tool2,
  Phabricator.isabelle_tool3,
  Phabricator.isabelle_tool4,
  Presentation.isabelle_tool,
  Profiling_Report.isabelle_tool,
  Server.isabelle_tool,
  Sessions.isabelle_tool,
  Scala_Project.isabelle_tool,
  Update.isabelle_tool,
  Update_Cartouches.isabelle_tool,
  Update_Comments.isabelle_tool,
  Update_Header.isabelle_tool,
  Update_Then.isabelle_tool,
  Update_Theorems.isabelle_tool,
  isabelle.vscode.TextMate_Grammar.isabelle_tool,
  isabelle.vscode.Language_Server.isabelle_tool)

class Admin_Tools extends Isabelle_Scala_Tools(
  Build_CSDP.isabelle_tool,
  Build_Cygwin.isabelle_tool,
  Build_Doc.isabelle_tool,
  Build_E.isabelle_tool,
  Build_Fonts.isabelle_tool,
  Build_JDK.isabelle_tool,
  Build_PolyML.isabelle_tool1,
  Build_PolyML.isabelle_tool2,
  Build_SPASS.isabelle_tool,
  Build_SQLite.isabelle_tool,
  Build_Status.isabelle_tool,
  Build_Vampire.isabelle_tool,
  Build_VeriT.isabelle_tool,
  Build_Zipperposition.isabelle_tool,
  Check_Sources.isabelle_tool,
  Components.isabelle_tool,
  isabelle.vscode.Build_VSCode.isabelle_tool)
