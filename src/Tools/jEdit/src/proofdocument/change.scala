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
  val parent: Option[Change],
  val edits: List[Edit],
  val id: Isar_Document.Document_ID,
  val result: Future[Document.Result])
{
  def ancestors: Iterator[Change] = new Iterator[Change]
  {
    private var state: Option[Change] = Some(Change.this)
    def hasNext = state.isDefined
    def next =
      state match {
        case Some(change) => state = change.parent; change
        case None => throw new NoSuchElementException("next on empty iterator")
      }
  }

  def document: Document = result.join._1
  def document_edits: List[Document.Structure_Edit] = result.join._2
}