/*  Title:      Tools/VSCode/src/document_model.scala
    Author:     Makarius

Document model for line-oriented text.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}

import scala.util.parsing.input.CharSequenceReader


object Document_Model
{
  def init(session: Session, uri: String): Document_Model =
  {
    val resources = session.resources.asInstanceOf[VSCode_Resources]
    val node_name = resources.node_name(uri)
    val doc = Line.Document("", resources.text_length)
    Document_Model(session, node_name, doc)
  }
}

sealed case class Document_Model(
  session: Session,
  node_name: Document.Node.Name,
  doc: Line.Document,
  external_file: Boolean = false,
  node_required: Boolean = false,
  last_perspective: Document.Node.Perspective_Text = Document.Node.no_perspective_text,
  pending_edits: Vector[Text.Edit] = Vector.empty,
  published_diagnostics: List[Text.Info[Command.Results]] = Nil)
{
  /* name */

  override def toString: String = node_name.toString

  def uri: String = node_name.node
  def is_theory: Boolean = node_name.is_theory


  /* external file */

  val file: JFile = VSCode_Resources.canonical_file(uri)

  def register(watcher: File_Watcher)
  {
    val dir = file.getParentFile
    if (dir != null && dir.isDirectory) watcher.register(dir)
  }


  /* header */

  def node_header: Document.Node.Header =
    resources.special_header(node_name) getOrElse
    {
      if (is_theory)
        resources.check_thy_reader(
          "", node_name, new CharSequenceReader(Thy_Header.header_text(doc)), Token.Pos.command)
      else Document.Node.no_header
    }


  /* perspective */

  def node_visible: Boolean = !external_file

  def text_perspective: Text.Perspective =
    if (node_visible) Text.Perspective.full else Text.Perspective.empty

  def node_perspective: Document.Node.Perspective_Text =
    Document.Node.Perspective(node_required, text_perspective, Document.Node.Overlays.empty)


  /* edits */

  def update_text(new_text: String): Option[Document_Model] =
  {
    val old_text = doc.make_text
    if (new_text == old_text) None
    else {
      val doc1 = Line.Document(new_text, doc.text_length)
      val pending_edits1 =
        if (old_text != "") pending_edits :+ Text.Edit.remove(0, old_text) else pending_edits
      val pending_edits2 = pending_edits1 :+ Text.Edit.insert(0, new_text)
      Some(copy(doc = doc1, pending_edits = pending_edits2))
    }
  }

  def update_file: Option[Document_Model] =
    if (external_file) {
      try { update_text(File.read(file)) }
      catch { case ERROR(_) => None }
    }
    else None

  def flush_edits: Option[(List[Document.Edit_Text], Document_Model)] =
  {
    val perspective = node_perspective
    if (pending_edits.nonEmpty || last_perspective != perspective) {
      val text_edits = pending_edits.toList
      val edits =
        session.header_edit(node_name, node_header) ::
        (if (text_edits.isEmpty) Nil
         else List[Document.Edit_Text](node_name -> Document.Node.Edits(text_edits))) :::
        (if (last_perspective == perspective) Nil
         else List[Document.Edit_Text](node_name -> perspective))
      Some((edits, copy(pending_edits = Vector.empty, last_perspective = perspective)))
    }
    else None
  }


  /* diagnostics */

  def publish_diagnostics(rendering: VSCode_Rendering)
    : Option[(List[Text.Info[Command.Results]], Document_Model)] =
  {
    val diagnostics = rendering.diagnostics
    if (diagnostics == published_diagnostics) None
    else Some(diagnostics, copy(published_diagnostics = diagnostics))
  }


  /* prover session */

  def resources: VSCode_Resources = session.resources.asInstanceOf[VSCode_Resources]

  def snapshot(): Document.Snapshot = session.snapshot(node_name, pending_edits.toList)

  def rendering(): VSCode_Rendering = new VSCode_Rendering(this, snapshot(), resources)
}
