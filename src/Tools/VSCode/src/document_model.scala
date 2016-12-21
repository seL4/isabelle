/*  Title:      Tools/VSCode/src/document_model.scala
    Author:     Makarius

Document model for line-oriented text.
*/

package isabelle.vscode


import isabelle._

import scala.util.parsing.input.CharSequenceReader


case class Document_Model(
  session: Session, doc: Line.Document, node_name: Document.Node.Name,
  changed: Boolean = true)
{
  /* header */

  def is_theory: Boolean = node_name.is_theory

  lazy val node_header: Document.Node.Header =
    if (is_theory) {
      val toks = Token.explode(Thy_Header.bootstrap_syntax.keywords, doc.text)
      val toks1 = toks.dropWhile(tok => !tok.is_command(Thy_Header.THEORY))
      toks1.iterator.zipWithIndex.collectFirst({ case (tok, i) if tok.is_begin => i }) match {
        case Some(i) =>
          session.resources.check_thy_reader("", node_name,
            new CharSequenceReader(toks1.take(i + 1).map(_.source).mkString), Token.Pos.command)
        case None => Document.Node.no_header
      }
    }
    else Document.Node.no_header


  /* edits */

  def text_edits: List[Text.Edit] =
    if (changed) List(Text.Edit.insert(0, doc.text)) else Nil

  def node_edits: List[Document.Edit_Text] =
    if (changed) {
      List(session.header_edit(node_name, node_header),
        node_name -> Document.Node.Clear(),
        node_name -> Document.Node.Edits(text_edits),
        node_name ->
          Document.Node.Perspective(true, Text.Perspective.full, Document.Node.Overlays.empty))
    }
    else Nil

  def unchanged: Document_Model = if (changed) copy(changed = false) else this


  /* snapshot and rendering */

  def snapshot(): Document.Snapshot = session.snapshot(node_name, text_edits)

  def rendering(options: Options): VSCode_Rendering =
    new VSCode_Rendering(this, snapshot(), options, session.resources)
}
