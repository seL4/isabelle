/*
 * Changes of plain text
 *
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.proofdocument


class Change(
  val parent: Option[Change],
  val edits: List[Text_Edit],
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