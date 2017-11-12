/*  Title:      Pure/Thy/thy_document_model.scala
    Author:     Makarius

Document model for theory files: no blobs, no edits, no overlays.
*/

package isabelle


object Thy_Document_Model
{
  def read_file(session: Session,
    node_name: Document.Node.Name,
    node_visible: Boolean = false): Thy_Document_Model =
  {
    val path = node_name.path
    if (!node_name.is_theory) error("Not a theory file: " + path)
    new Thy_Document_Model(session, node_name, File.read(path), node_visible)
  }
}

final class Thy_Document_Model private(
  val session: Session,
  val node_name: Document.Node.Name,
  val text: String,
  val node_visible: Boolean) extends Document.Model
{
  /* content */

  def get_text(range: Text.Range): Option[String] =
    if (0 <= range.start && range.stop <= text.length) Some(range.substring(text)) else None

  def get_blob: Option[Document.Blob] = None

  def bibtex_entries: List[Text.Info[String]] = Nil


  /* header */

  def node_header: Document.Node.Header =
    resources.check_thy_reader(node_name, Scan.char_reader(text))

  def node_required: Boolean = true


  /* perspective */

  def text_perspective: Text.Perspective =
    if (node_visible) Text.Perspective.full else Text.Perspective.empty

  def node_perspective: Document.Node.Perspective_Text =
    Document.Node.Perspective(node_required, text_perspective, Document.Node.Overlays.empty)


  /* edits */

  def node_edits(old: Option[Thy_Document_Model]): List[Document.Edit_Text] =
  {
    val text_edits =
      if (old.isEmpty) Text.Edit.inserts(0, text)
      else Text.Edit.replace(0, old.get.text, text)

    if (text_edits.isEmpty && old.isDefined && old.get.node_perspective == node_perspective) Nil
    else node_edits(node_header, text_edits, node_perspective)
  }


  /* prover session */

  def resources: Resources = session.resources

  def is_stable: Boolean = true
  def snapshot(): Document.Snapshot = session.snapshot(node_name, pending_edits = Nil)
}
