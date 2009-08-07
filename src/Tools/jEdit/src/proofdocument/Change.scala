/*
 * Changes in text
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.proofdocument

abstract class Edit {
  val start: Int
  def from_where (x: Int): Int //where has x been before applying this edit
  def where_to(x: Int): Int //where will x be when we apply this edit
}

case class Insert(start: Int, added: String) extends Edit {
  def from_where(x: Int) =
    if (start <= x && start + added.length <= x) x - added.length else x

  def where_to(x: Int) =
    if (start <= x) x + added.length else x
}

case class Remove(start: Int, removed: String) extends Edit {
  def from_where(x: Int) =
    if (start <= x) x + removed.length else x

  def where_to(x: Int) =
    if (start <= x && start + removed.length <= x) x - removed.length else x
}
// TODO: merge multiple inserts?

class Change(
  val id: String,
  val parent: Option[Change],
  edits: List[Edit]) extends Iterable[Edit]
{
  override def elements = edits.reverse.elements

  def ancestors(root_p: Change => Boolean): List[Change] =
    if (root_p(this)) Nil
    else this :: parent.map(_.ancestors(root_p)).getOrElse(Nil)
  def ancestors: List[Change] = ancestors(_ => false)

  override def toString =
    "Change(" + id + " <- " + parent.map(_.id) + ", " + edits + ")"
}