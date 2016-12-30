/*  Title:      Tools/VSCode/src/document_model.scala
    Author:     Makarius

Document model for line-oriented text.
*/

package isabelle.vscode


import isabelle._

import scala.util.parsing.input.CharSequenceReader


object Document_Model
{
  def init(session: Session, node_name: Document.Node.Name, text: String): Document_Model =
  {
    val resources = session.resources.asInstanceOf[VSCode_Resources]
    Document_Model(session, node_name, Line.Document(text, resources.text_length),
      pending_clear = true,
      pending_edits = List(Text.Edit.insert(0, text)))
  }
}

sealed case class Document_Model private(
  session: Session,
  node_name: Document.Node.Name,
  doc: Line.Document,
  node_visible: Boolean = true,
  node_required: Boolean = false,
  last_perspective: Document.Node.Perspective_Text = Document.Node.no_perspective_text,
  pending_clear: Boolean = false,
  pending_edits: List[Text.Edit] = Nil,
  published_diagnostics: List[Text.Info[Command.Results]] = Nil)
{
  /* name */

  override def toString: String = node_name.toString

  def uri: String = node_name.node
  def is_theory: Boolean = node_name.is_theory


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

  def text_perspective: Text.Perspective =
    if (node_visible) Text.Perspective.full else Text.Perspective.empty

  def node_perspective: Document.Node.Perspective_Text =
    Document.Node.Perspective(node_required, text_perspective, Document.Node.Overlays.empty)


  /* edits */

  def flush_edits: Option[(List[Document.Edit_Text], Document_Model)] =
  {
    val perspective = node_perspective
    if (pending_clear || pending_edits.nonEmpty || last_perspective != perspective) {
      val model1 = copy(pending_clear = false, pending_edits = Nil, last_perspective = perspective)

      val header_edit = session.header_edit(node_name, node_header)
      val edits: List[Document.Edit_Text] =
        if (pending_clear)
          List(header_edit,
            node_name -> Document.Node.Clear(),
            node_name -> Document.Node.Edits(pending_edits),
            node_name -> perspective)
        else
          List(header_edit,
            node_name -> Document.Node.Edits(pending_edits),
            node_name -> perspective)

      Some((edits.filterNot(_._2.is_void), model1))
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


  /* session */

  def resources: VSCode_Resources = session.resources.asInstanceOf[VSCode_Resources]

  def snapshot(): Document.Snapshot = session.snapshot(node_name, pending_edits)

  def rendering(): VSCode_Rendering = new VSCode_Rendering(this, snapshot(), resources)
}
