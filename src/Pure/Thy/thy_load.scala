/*  Title:      Pure/Thy/thy_load.scala
    Author:     Makarius

Loading files that contribute to a theory.
*/

package isabelle

abstract class Thy_Load
{
  def check_thy(dir: Path, name: String): (String, Thy_Header.Header)
}

