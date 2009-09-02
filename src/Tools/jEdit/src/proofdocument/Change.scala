/*
 * Changes in text
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.proofdocument

sealed abstract class Edit
{
  val start: Int
  def from_where (x: Int): Int //where has x been before applying this edit
  def where_to(x: Int): Int //where will x be when we apply this edit
}

case class Insert(start: Int, text: String) extends Edit
{
  def from_where(x: Int) =
    if (start > x) x
    else (x - text.length) max start

  def where_to(x: Int) =
    if (start <= x) x + text.length else x
}

case class Remove(start: Int, text: String) extends Edit
{
  def from_where(x: Int) =
    if (start <= x) x + text.length else x

  def where_to(x: Int) =
    if (start > x) x
    else (x - text.length) max start
}
// TODO: merge multiple inserts?

class Change(
  val id: String,
  val parent: Option[Change],
  val edits: List[Edit])
{
  def ancestors(done: Change => Boolean): List[Change] =
    if (done(this)) Nil
    else this :: parent.map(_.ancestors(done)).getOrElse(Nil)
  def ancestors: List[Change] = ancestors(_ => false)

  override def toString =
    "Change(" + id + " <- " + parent.map(_.id) + ", " + edits + ")"
}