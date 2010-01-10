/*
 * Changes of plain text
 *
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.proofdocument


class Change(
  val id: Isar_Document.Document_ID,
  val parent: Option[Change],
  val edits: List[Text_Edit],
  val result: Future[(List[Document.Edit], Document)])
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

  def join_document: Document = result.join._2

  def edit(session: Session, edits: List[Text_Edit]): Change =
  {
    val new_id = session.create_id()
    val result: Future[(List[Document.Edit], Document)] =
      Future.fork {
        val old_doc = join_document
        old_doc.await_assignment
        Document.text_edits(session, old_doc, new_id, edits)
      }
    new Change(new_id, Some(this), edits, result)
  }
}