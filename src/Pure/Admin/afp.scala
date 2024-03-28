/*  Title:      Pure/Admin/afp.scala
    Author:     Makarius

Administrative support for the Archive of Formal Proofs.
*/

package isabelle


object AFP {
  val chapter: String = "AFP"

  val BASE: Path = Path.explode("$AFP_BASE")

  def main_dir(base_dir: Path = BASE): Path = base_dir + Path.explode("thys")

  def main_dirs(afp_root: Option[Path]): List[Path] =
    afp_root match {
      case None => Nil
      case Some(base_dir) => List(main_dir(base_dir = base_dir))
    }
}
