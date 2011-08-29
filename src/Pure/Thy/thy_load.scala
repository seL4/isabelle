/*  Title:      Pure/Thy/thy_load.scala
    Author:     Makarius

Loading files that contribute to a theory.
*/

package isabelle

abstract class Thy_Load
{
  def register_thy(thy_name: String)
  def is_loaded(thy_name: String): Boolean
  def append(master_dir: String, path: Path): String
  def check_thy(node_name: String): Thy_Header
}

