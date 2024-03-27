/*  Title:      Pure/System/setup_tool.scala
    Author:     Makarius

Additional setup tools for other Isabelle distribution.
*/

package isabelle


object Setup_Tool {
  lazy val services: List[Setup_Tool] =
    Isabelle_System.make_services(classOf[Setup_Tool])

  def init(other_isabelle: Other_Isabelle, verbose: Boolean = false): Unit =
    services.foreach(_.init(other_isabelle, verbose = verbose))
}

abstract class Setup_Tool(tool: String)
extends Isabelle_System.Service {
  override def toString: String = tool

  val variable: String = "ISABELLE_" + Word.uppercase(tool)
  val files: List[Path] = List(Path.explode("lib/Tools") + Path.basic(tool))

  def test(other_isabelle: Other_Isabelle): Boolean =
    other_isabelle.getenv(variable) == "true" &&
    files.exists(p => (other_isabelle.isabelle_home + p).is_file)

  def run(other_isabelle: Other_Isabelle, verbose: Boolean = false): Unit =
    other_isabelle.bash("bin/isabelle " + Bash.string(tool), echo = verbose)

  def init(other_isabelle: Other_Isabelle, verbose: Boolean = false): Unit =
    if (test(other_isabelle)) run(other_isabelle, verbose = verbose)
}

class GHC_Setup extends Setup_Tool("ghc_setup")
class OCaml_Setup extends Setup_Tool("ocaml_setup")
