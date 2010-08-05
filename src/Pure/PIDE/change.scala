/*  Title:      Pure/PIDE/change.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Changes of plain text, resulting in document edits.
*/

package isabelle


object Change
{
  val init = new Change(Document.NO_ID, None, Nil, Future.value(Nil, Document.init))

  abstract class Snapshot
  {
    val document: Document
    val node: Document.Node
    val is_outdated: Boolean
    def convert(offset: Int): Int
    def revert(offset: Int): Int
  }
}

class Change(
  val id: Document.Version_ID,
  val parent: Option[Change],
  val edits: List[Document.Node_Text_Edit],
  val result: Future[(List[Document.Edit[Command]], Document)])
{
  /* ancestor versions */

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


  /* editing and state assignment */

  def edit(session: Session, edits: List[Document.Node_Text_Edit]): Change =
  {
    val new_id = session.create_id()
    val result: Future[(List[Document.Edit[Command]], Document)] =
      Future.fork {
        val old_doc = join_document
        old_doc.await_assignment
        Document.text_edits(session, old_doc, new_id, edits)
      }
    new Change(new_id, Some(this), edits, result)
  }

  def join_document: Document = result.join._2
  def is_assigned: Boolean = result.is_finished && join_document.assignment.is_finished


  /* snapshot */

  def snapshot(name: String, extra_edits: List[Text_Edit]): Change.Snapshot =
  {
    val latest = this
    val stable = latest.ancestors.find(_.is_assigned).get
    val changes =
      (extra_edits /: latest.ancestors.takeWhile(_ != stable))((edits, change) =>
          (for ((a, eds) <- change.edits if a == name) yield eds).flatten ::: edits)

    new Change.Snapshot {
      val document = stable.join_document
      val node = document.nodes(name)
      val is_outdated = !(extra_edits.isEmpty && latest == stable)
      def convert(offset: Int): Int = (offset /: changes)((i, change) => change.convert(i))
      def revert(offset: Int): Int = (offset /: changes.reverse)((i, change) => change.revert(i))  // FIXME fold_rev (!?)
    }
  }
}