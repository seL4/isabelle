/*  Title:      Pure/Thy/thy_document_model.scala
    Author:     Makarius

Document model for theory files: no edits, no blobs, no overlays.
*/

package isabelle


object Thy_Document_Model
{
  def read_file(session: Session, path: Path,
    qualifier: String = Sessions.DRAFT,
    node_visible: Boolean = false,
    node_required: Boolean = false): Thy_Document_Model =
  {
    val node_name = session.resources.thy_node_name(qualifier, path.file)
    if (!node_name.is_theory) error("Not a theory file: " + path)
    new Thy_Document_Model(session, node_name, File.read(path), node_visible, node_required)
  }
}

final class Thy_Document_Model private(
  val session: Session,
  val node_name: Document.Node.Name,
  val text: String,
  val node_visible: Boolean,
  val node_required: Boolean) extends Document.Model
{
  /* content */

  def get_text(range: Text.Range): Option[String] =
    if (0 <= range.start && range.stop <= text.length) Some(range.substring(text)) else None

  def get_blob: Option[Document.Blob] = None

  def bibtex_entries: List[Text.Info[String]] = Nil


  /* header */

  def node_header: Document.Node.Header =
    resources.check_thy_reader(node_name, Scan.char_reader(text))


  /* perspective */

  def text_perspective: Text.Perspective =
    if (node_visible) Text.Perspective.full else Text.Perspective.empty

  def node_perspective: Document.Node.Perspective_Text =
    Document.Node.Perspective(node_required, text_perspective, Document.Node.Overlays.empty)


  /* prover session */

  def resources: Resources = session.resources

  def is_stable: Boolean = true
  def snapshot(): Document.Snapshot = session.snapshot(node_name, pending_edits = Nil)
}
