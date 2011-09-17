/*  Title:      Pure/Thy/thy_load.scala
    Author:     Makarius

Primitives for loading theory files.
*/

package isabelle


import java.io.File



class Thy_Load
{
  /* loaded theories provided by prover */

  private var loaded_theories: Set[String] = Set()

  def register_thy(thy_name: String): Unit =
    synchronized { loaded_theories += thy_name }

  def is_loaded(thy_name: String): Boolean =
    synchronized { loaded_theories.contains(thy_name) }


  /* file-system operations */

  def append(dir: String, source_path: Path): String =
    (Path.explode(dir) + source_path).implode

  def check_thy(name: Document.Node.Name): Thy_Header =
  {
    val file = new File(name.node)
    if (!file.exists || !file.isFile) error("No such file: " + quote(file.toString))
    Thy_Header.read(file)
  }
}

