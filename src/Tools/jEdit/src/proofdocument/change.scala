/*
 * Changes of plain text
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.proofdocument


import scala.actors.Future


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
  val id: Isar_Document.Document_ID,
  val parent: Option[Change],
  val edits: List[Edit],
  val result: Future[Document.Result])
{
  // FIXME iterator
  def ancestors(done: Change => Boolean): List[Change] =
    if (done(this)) Nil
    else this :: parent.map(_.ancestors(done)).getOrElse(Nil)
  def ancestors: List[Change] = ancestors(_ => false)

  def document: Document = result()._1
  def document_edits: List[Document.Structure_Edit] = result()._2
}