/*  Title:      Tools/VSCode/src/document_model.scala
    Author:     Makarius

Document model for line-oriented text.
*/

package isabelle.vscode


import isabelle._

import scala.util.parsing.input.CharSequenceReader


case class Document_Model(
  session: Session, doc: Line.Document, node_name: Document.Node.Name,
  changed: Boolean = true,
  published_diagnostics: List[Text.Info[Command.Results]] = Nil)
{
  override def toString: String = node_name.toString


  /* name */

  def uri: String = node_name.node
  def is_theory: Boolean = node_name.is_theory


  /* header */

  def node_header(resources: VSCode_Resources): Document.Node.Header =
    resources.special_header(node_name) getOrElse
    {
      if (is_theory)
        session.resources.check_thy_reader(
          "", node_name, new CharSequenceReader(Thy_Header.header_text(doc)), Token.Pos.command)
      else Document.Node.no_header
    }


  /* edits */

  def text_edits: List[Text.Edit] =
    if (changed) List(Text.Edit.insert(0, doc.make_text)) else Nil

  def node_edits(resources: VSCode_Resources): List[Document.Edit_Text] =
    if (changed) {
      List(session.header_edit(node_name, node_header(resources)),
        node_name -> Document.Node.Clear(),
        node_name -> Document.Node.Edits(text_edits),
        node_name ->
          Document.Node.Perspective(true, Text.Perspective.full, Document.Node.Overlays.empty))
    }
    else Nil

  def unchanged: Document_Model = if (changed) copy(changed = false) else this


  /* diagnostics */

  def publish_diagnostics(rendering: VSCode_Rendering)
    : Option[(List[Text.Info[Command.Results]], Document_Model)] =
  {
    val diagnostics = rendering.diagnostics
    if (diagnostics == published_diagnostics) None
    else Some(diagnostics, copy(published_diagnostics = diagnostics))
  }


  /* snapshot and rendering */

  def snapshot(): Document.Snapshot = session.snapshot(node_name, text_edits)

  def rendering(options: Options): VSCode_Rendering =
    new VSCode_Rendering(this, snapshot(), options, session.resources)
}
