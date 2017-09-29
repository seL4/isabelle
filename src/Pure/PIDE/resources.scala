/*  Title:      Pure/PIDE/resources.scala
    Author:     Makarius

Resources for theories and auxiliary files.
*/

package isabelle


import scala.annotation.tailrec
import scala.util.parsing.input.Reader

import java.io.{File => JFile}


class Resources(
  val session_base: Sessions.Base,
  val log: Logger = No_Logger)
{
  val thy_info = new Thy_Info(this)

  def thy_path(path: Path): Path = path.ext("thy")


  /* file-system operations */

  def append(dir: String, source_path: Path): String =
    (Path.explode(dir) + source_path).expand.implode

  def append(node_name: Document.Node.Name, source_path: Path): String =
    append(node_name.master_dir, source_path)


  /* source files of Isabelle/ML bootstrap */

  def source_file(raw_name: String): Option[String] =
  {
    if (Path.is_wellformed(raw_name)) {
      if (Path.is_valid(raw_name)) {
        def check(p: Path): Option[Path] = if (p.is_file) Some(p) else None

        val path = Path.explode(raw_name)
        val path1 =
          if (path.is_absolute || path.is_current) check(path)
          else {
            check(Path.explode("~~/src/Pure") + path) orElse
              (if (Isabelle_System.getenv("ML_SOURCES") == "") None
               else check(Path.explode("$ML_SOURCES") + path))
          }
        Some(File.platform_path(path1 getOrElse path))
      }
      else None
    }
    else Some(raw_name)
  }


  /* theory files */

  def loaded_files(syntax: Outer_Syntax, name: Document.Node.Name): () => List[Path] =
  {
    val raw_text = with_thy_reader(name, reader => reader.source.toString)
    () => {
      val text = Symbol.decode(raw_text)
      if (syntax.load_commands_in(text)) {
        val spans = syntax.parse_spans(text)
        val dir = Path.explode(name.master_dir)
        spans.iterator.map(Command.span_files(syntax, _)._1).flatten.
          map(a => (dir + Path.explode(a)).expand).toList
      }
      else Nil
    }
  }

  def pure_files(syntax: Outer_Syntax, dir: Path): List[Path] =
  {
    val roots =
      for { (name, _) <- Thy_Header.ml_roots }
      yield (dir + Path.explode(name)).expand
    val files =
      for {
        (path, (_, theory)) <- roots zip Thy_Header.ml_roots
        file <- loaded_files(syntax, Document.Node.Name(path.implode, path.dir.implode, theory))()
      } yield file
    roots ::: files
  }

  def theory_qualifier(name: Document.Node.Name): String =
    session_base.global_theories.getOrElse(name.theory, Long_Name.qualifier(name.theory))

  def theory_name(qualifier: String, theory: String): (Boolean, String) =
    if (session_base.loaded_theory(theory)) (true, theory)
    else {
      val theory1 =
        if (Long_Name.is_qualified(theory) || session_base.global_theories.isDefinedAt(theory))
          theory
        else Long_Name.qualify(qualifier, theory)
      (false, theory1)
    }

  def import_name(qualifier: String, dir: String, s: String): Document.Node.Name =
    theory_name(qualifier, Thy_Header.import_name(s)) match {
      case (true, theory) => Document.Node.Name.loaded_theory(theory)
      case (false, theory) =>
        session_base.known_theory(theory) match {
          case Some(node_name) => node_name
          case None =>
            val path = Path.explode(s)
            val node = append(dir, thy_path(path))
            val master_dir = append(dir, path.dir)
            Document.Node.Name(node, master_dir, theory)
        }
    }

  def import_name(name: Document.Node.Name, s: String): Document.Node.Name =
    import_name(theory_qualifier(name), name.master_dir, s)

  def with_thy_reader[A](name: Document.Node.Name, f: Reader[Char] => A): A =
  {
    val path = File.check_file(name.path)
    val reader = Scan.byte_reader(path.file)
    try { f(reader) } finally { reader.close }
  }

  def check_thy_reader(node_name: Document.Node.Name, reader: Reader[Char],
    start: Token.Pos = Token.Pos.command, strict: Boolean = true): Document.Node.Header =
  {
    if (node_name.is_theory && reader.source.length > 0) {
      try {
        val header = Thy_Header.read(reader, start, strict)

        val base_name = node_name.theory_base_name
        val (name, pos) = header.name
        if (base_name != name)
          error("Bad theory name " + quote(name) +
            " for file " + thy_path(Path.basic(base_name)) + Position.here(pos) +
            Completion.report_names(pos, 1, List((base_name, ("theory", base_name)))))

        val imports = header.imports.map({ case (s, pos) => (import_name(node_name, s), pos) })
        Document.Node.Header(imports, header.keywords, header.abbrevs)
      }
      catch { case exn: Throwable => Document.Node.bad_header(Exn.message(exn)) }
    }
    else Document.Node.no_header
  }

  def check_thy(name: Document.Node.Name, start: Token.Pos = Token.Pos.command,
      strict: Boolean = true): Document.Node.Header =
    with_thy_reader(name, check_thy_reader(name, _, start, strict))


  /* special header */

  def special_header(name: Document.Node.Name): Option[Document.Node.Header] =
  {
    val imports =
      if (Thy_Header.is_ml_root(name.theory)) List(import_name(name, Thy_Header.ML_BOOTSTRAP))
      else if (Thy_Header.is_bootstrap(name.theory)) List(import_name(name, Thy_Header.PURE))
      else Nil
    if (imports.isEmpty) None
    else Some(Document.Node.Header(imports.map((_, Position.none))))
  }


  /* blobs */

  def undefined_blobs(nodes: Document.Nodes): List[Document.Node.Name] =
    (for {
      (node_name, node) <- nodes.iterator
      if !session_base.loaded_theory(node_name)
      cmd <- node.load_commands.iterator
      name <- cmd.blobs_undefined.iterator
    } yield name).toList


  /* document changes */

  def parse_change(
      reparse_limit: Int,
      previous: Document.Version,
      doc_blobs: Document.Blobs,
      edits: List[Document.Edit_Text]): Session.Change =
    Thy_Syntax.parse_change(this, reparse_limit, previous, doc_blobs, edits)

  def commit(change: Session.Change) { }
}
