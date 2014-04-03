/*  Title:      Pure/PIDE/resources.scala
    Author:     Makarius

Resources for theories and auxiliary files.
*/

package isabelle


import scala.annotation.tailrec

import java.io.{File => JFile}


object Resources
{
  def thy_path(path: Path): Path = path.ext("thy")
}


class Resources(val loaded_theories: Set[String] = Set.empty, val base_syntax: Prover.Syntax)
{
  /* document node names */

  def node_name(raw_path: Path): Document.Node.Name =
  {
    val path = raw_path.expand
    val node = path.implode
    val theory = Thy_Header.thy_name(node).getOrElse("")
    val master_dir = if (theory == "") "" else path.dir.implode
    Document.Node.Name(node, master_dir, theory)
  }


  /* file-system operations */

  def append(dir: String, source_path: Path): String =
    (Path.explode(dir) + source_path).expand.implode

  def with_thy_text[A](name: Document.Node.Name, f: CharSequence => A): A =
  {
    val path = Path.explode(name.node)
    if (!path.is_file) error("No such file: " + path.toString)

    val text = File.read(path)
    Symbol.decode_strict(text)
    f(text)
  }


  /* theory files */

  def loaded_files(syntax: Prover.Syntax, text: String): List[String] =
    if (syntax.load_commands_in(text)) {
      val spans = Thy_Syntax.parse_spans(syntax.scan(text))
      spans.iterator.map(Thy_Syntax.span_files(syntax, _)).flatten.toList
    }
    else Nil

  def import_name(master: Document.Node.Name, s: String): Document.Node.Name =
  {
    val theory = Thy_Header.base_name(s)
    if (loaded_theories(theory)) Document.Node.Name(theory + ".thy", "", theory)
    else {
      val path = Path.explode(s)
      val node = append(master.master_dir, Resources.thy_path(path))
      val master_dir = append(master.master_dir, path.dir)
      Document.Node.Name(node, master_dir, theory)
    }
  }

  def check_thy_text(name: Document.Node.Name, text: CharSequence): Document.Node.Header =
  {
    try {
      val header = Thy_Header.read(text)

      val name1 = header.name
      if (name.theory != name1)
        error("Bad file name " + Resources.thy_path(Path.basic(name.theory)) +
          " for theory " + quote(name1))

      val imports = header.imports.map(import_name(name, _))
      Document.Node.Header(imports, header.keywords, Nil)
    }
    catch { case exn: Throwable => Document.Node.bad_header(Exn.message(exn)) }
  }

  def check_thy(name: Document.Node.Name): Document.Node.Header =
    with_thy_text(name, check_thy_text(name, _))


  /* document changes */

  def parse_change(
      reparse_limit: Int,
      previous: Document.Version,
      doc_blobs: Document.Blobs,
      edits: List[Document.Edit_Text]): Session.Change =
    Thy_Syntax.parse_change(this, reparse_limit, previous, doc_blobs, edits)

  def commit(change: Session.Change) { }


  /* prover process */

  def start_prover(receiver: Prover.Message => Unit, name: String, args: List[String]): Prover =
    new Isabelle_Process(receiver, args) with Protocol
}

