/*
 * Changes of plain text
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.proofdocument


sealed abstract class Edit
{
  val start: Int
  def before(offset: Int): Int
  def after(offset: Int): Int
}


case class Insert(start: Int, text: String) extends Edit
{
  def before(offset: Int): Int =
    if (start > offset) offset
    else (offset - text.length) max start

  def after(offset: Int): Int =
    if (start <= offset) offset + text.length else offset
}


case class Remove(start: Int, text: String) extends Edit
{
  def before(offset: Int): Int =
    if (start <= offset) offset + text.length else offset

  def after(offset: Int): Int =
    if (start > offset) offset
    else (offset - text.length) max start
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