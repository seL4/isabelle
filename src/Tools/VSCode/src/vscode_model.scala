/*  Title:      Tools/VSCode/src/vscode_model.scala
    Author:     Makarius

VSCode document model for line-oriented text.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}


object VSCode_Model
{
  /* decorations */

  object Decoration
  {
    def empty(typ: String): Decoration = Decoration(typ, Nil)

    def ranges(typ: String, ranges: List[Text.Range]): Decoration =
      Decoration(typ, ranges.map(Text.Info(_, List.empty[XML.Body])))
  }
  sealed case class Decoration(typ: String, content: List[Text.Info[List[XML.Body]]])


  /* content */

  object Content
  {
    val empty: Content = Content(Line.Document.empty)
  }

  sealed case class Content(doc: Line.Document)
  {
    override def toString: String = doc.toString
    def text_length: Text.Offset = doc.text_length
    def text_range: Text.Range = doc.text_range
    def text: String = doc.text

    lazy val bytes: Bytes = Bytes(text)
    lazy val chunk: Symbol.Text_Chunk = Symbol.Text_Chunk(text)
    lazy val bibtex_entries: List[Text.Info[String]] =
      try { Bibtex.entries(text) }
      catch { case ERROR(_) => Nil }

    def recode_symbols: List[LSP.TextEdit] =
      (for {
        (line, l) <- doc.lines.iterator.zipWithIndex
        text1 = Symbol.encode(line.text)
        if (line.text != text1)
      } yield {
        val range = Line.Range(Line.Position(l), Line.Position(l, line.text.length))
        LSP.TextEdit(range, text1)
      }).toList
  }

  def init(session: Session, editor: Language_Server.Editor, node_name: Document.Node.Name)
    : VSCode_Model =
  {
    VSCode_Model(session, editor, node_name, Content.empty,
      node_required = File_Format.registry.is_theory(node_name))
  }
}

sealed case class VSCode_Model(
  session: Session,
  editor: Language_Server.Editor,
  node_name: Document.Node.Name,
  content: VSCode_Model.Content,
  version: Option[Long] = None,
  external_file: Boolean = false,
  node_required: Boolean = false,
  last_perspective: Document.Node.Perspective_Text = Document.Node.no_perspective_text,
  pending_edits: List[Text.Edit] = Nil,
  published_diagnostics: List[Text.Info[Command.Results]] = Nil,
  published_decorations: List[VSCode_Model.Decoration] = Nil) extends Document.Model
{
  model =>


  /* content */

  def get_text(range: Text.Range): Option[String] = content.doc.get_text(range)

  def set_version(new_version: Long): VSCode_Model = copy(version = Some(new_version))


  /* external file */

  def external(b: Boolean): VSCode_Model = copy(external_file = b)

  def node_visible: Boolean = !external_file


  /* header */

  def node_header: Document.Node.Header =
    resources.special_header(node_name) getOrElse
      resources.check_thy_reader(node_name, Scan.char_reader(content.text))


  /* perspective */

  def node_perspective(doc_blobs: Document.Blobs, caret: Option[Line.Position])
    : (Boolean, Document.Node.Perspective_Text) =
  {
    if (is_theory) {
      val snapshot = model.snapshot()

      val caret_perspective = resources.options.int("vscode_caret_perspective") max 0
      val caret_range =
        if (caret_perspective != 0) {
          caret match {
            case Some(pos) =>
              val doc = content.doc
              val pos1 = Line.Position((pos.line - caret_perspective) max 0)
              val pos2 = Line.Position((pos.line + caret_perspective + 1) min doc.lines.length)
              Text.Range(doc.offset(pos1).get, doc.offset(pos2).get)
            case None => Text.Range.offside
          }
        }
        else if (node_visible) content.text_range
        else Text.Range.offside

      val text_perspective =
        if (snapshot.commands_loading_ranges(resources.visible_node(_)).nonEmpty)
          Text.Perspective.full
        else
          content.text_range.try_restrict(caret_range) match {
            case Some(range) => Text.Perspective(List(range))
            case None => Text.Perspective.empty
          }

      val overlays = editor.node_overlays(node_name)

      (snapshot.node.load_commands_changed(doc_blobs),
        Document.Node.Perspective(node_required, text_perspective, overlays))
    }
    else (false, Document.Node.no_perspective_text)
  }


  /* blob */

  def get_blob: Option[Document.Blob] =
    if (is_theory) None
    else Some(Document.Blob(content.bytes, content.text, content.chunk, pending_edits.nonEmpty))


  /* bibtex entries */

  def bibtex_entries: List[Text.Info[String]] =
    model.content.bibtex_entries


  /* edits */

  def change_text(text: String, range: Option[Line.Range] = None): Option[VSCode_Model] =
  {
    val insert = Line.normalize(text)
    range match {
      case None =>
        Text.Edit.replace(0, content.text, insert) match {
          case Nil => None
          case edits =>
            val content1 = VSCode_Model.Content(Line.Document(insert))
            Some(copy(content = content1, pending_edits = pending_edits ::: edits))
        }
      case Some(remove) =>
        content.doc.change(remove, insert) match {
          case None => error("Failed to apply document change: " + remove)
          case Some((Nil, _)) => None
          case Some((edits, doc1)) =>
            val content1 = VSCode_Model.Content(doc1)
            Some(copy(content = content1, pending_edits = pending_edits ::: edits))
        }
    }
  }

  def flush_edits(
      unicode_symbols: Boolean,
      doc_blobs: Document.Blobs,
      file: JFile,
      caret: Option[Line.Position])
    : Option[((List[LSP.TextDocumentEdit], List[Document.Edit_Text]), VSCode_Model)] =
  {
    val workspace_edits =
      if (unicode_symbols && version.isDefined) {
        val edits = content.recode_symbols
        if (edits.nonEmpty) List(LSP.TextDocumentEdit(file, version.get, edits))
        else Nil
      }
      else Nil

    val (reparse, perspective) = node_perspective(doc_blobs, caret)
    if (reparse || pending_edits.nonEmpty || last_perspective != perspective ||
        workspace_edits.nonEmpty)
    {
      val prover_edits = node_edits(node_header, pending_edits, perspective)
      val edits = (workspace_edits, prover_edits)
      Some((edits, copy(pending_edits = Nil, last_perspective = perspective)))
    }
    else None
  }


  /* publish annotations */

  def publish(rendering: VSCode_Rendering):
    (Option[List[Text.Info[Command.Results]]], Option[List[VSCode_Model.Decoration]], VSCode_Model) =
  {
    val diagnostics = rendering.diagnostics
    val decorations =
      if (node_visible) rendering.decorations
      else { for (deco <- published_decorations) yield VSCode_Model.Decoration.empty(deco.typ) }

    val changed_diagnostics =
      if (diagnostics == published_diagnostics) None else Some(diagnostics)
    val changed_decorations =
      if (decorations == published_decorations) None
      else if (published_decorations.isEmpty) Some(decorations)
      else Some(for { (a, b) <- decorations zip published_decorations if a != b } yield a)

    (changed_diagnostics, changed_decorations,
      copy(published_diagnostics = diagnostics, published_decorations = decorations))
  }


  /* prover session */

  def resources: VSCode_Resources = session.resources.asInstanceOf[VSCode_Resources]

  def is_stable: Boolean = pending_edits.isEmpty
  def snapshot(): Document.Snapshot = session.snapshot(node_name, pending_edits)

  def rendering(snapshot: Document.Snapshot): VSCode_Rendering =
    new VSCode_Rendering(snapshot, model)
  def rendering(): VSCode_Rendering = rendering(snapshot())


  /* syntax */

  def syntax(): Outer_Syntax =
    if (is_theory) session.recent_syntax(node_name) else Outer_Syntax.empty
}
