/*  Title:      Pure/Thy/thy_load.scala
    Author:     Makarius

Primitives for loading theory files.
*/

package isabelle


import scala.annotation.tailrec

import java.io.{File => JFile}


object Thy_Load
{
  def thy_path(path: Path): Path = path.ext("thy")

  def is_ok(str: String): Boolean =
    try { thy_path(Path.explode(str)); true }
    catch { case ERROR(_) => false }
}


class Thy_Load(val loaded_theories: Set[String] = Set.empty, val base_syntax: Outer_Syntax)
{
  /* file-system operations */

  def append(dir: String, source_path: Path): String =
    (Path.explode(dir) + source_path).expand.implode

  def with_thy_text[A](name: Document.Node.Name, f: CharSequence => A): A =
  {
    val path = Path.explode(name.node)
    if (!path.is_file) error("No such file: " + path.toString)
    f(File.read(path))
  }


  /* theory files */

  private def import_name(dir: String, s: String): Document.Node.Name =
  {
    val theory = Thy_Header.base_name(s)
    if (loaded_theories(theory)) Document.Node.Name(theory, "", theory)
    else {
      val path = Path.explode(s)
      val node = append(dir, Thy_Load.thy_path(path))
      val dir1 = append(dir, path.dir)
      Document.Node.Name(node, dir1, theory)
    }
  }

  private def find_file(tokens: List[Token]): Option[String] =
  {
    def clean(toks: List[Token]): List[Token] =
      toks match {
        case t :: _ :: ts if t.is_keyword && (t.source == "%" || t.source == "--") => clean(ts)
        case t :: ts => t :: clean(ts)
        case Nil => Nil
      }
    val clean_tokens = clean(tokens.filter(_.is_proper))
    clean_tokens.reverse.find(_.is_name).map(_.content)
  }

  def find_files(syntax: Outer_Syntax, text: String): List[String] =
  {
    val thy_load_commands = syntax.thy_load_commands
    if (thy_load_commands.exists({ case (cmd, _) => text.containsSlice(cmd) })) {
      val spans = Thy_Syntax.parse_spans(syntax.scan(text))
      spans.iterator.map({
        case toks @ (tok :: _) if tok.is_command =>
          thy_load_commands.find({ case (cmd, _) => cmd == tok.content }) match {
            case Some((_, exts)) =>
              find_file(toks) match {
                case Some(file) =>
                  if (exts.isEmpty) List(file)
                  else exts.map(ext => file + "." + ext)
                case None => Nil
              }
            case None => Nil
          }
        case _ => Nil
      }).flatten.toList
    }
    else Nil
  }

  def check_thy_text(name: Document.Node.Name, text: CharSequence): Document.Node.Header =
  {
    val header = Thy_Header.read(text)

    val name1 = header.name
    if (name.theory != name1)
      error("Bad file name " + Thy_Load.thy_path(Path.basic(name.theory)) +
        " for theory " + quote(name1))

    val imports = header.imports.map(import_name(name.dir, _))
    val uses = header.uses
    Document.Node.Header(imports, header.keywords, uses)
  }

  def check_thy(name: Document.Node.Name): Document.Node.Header =
    with_thy_text(name, check_thy_text(name, _))

  def check_thy_files(syntax: Outer_Syntax, name: Document.Node.Name): Document.Node.Header =
    with_thy_text(name, text =>
      {
        val string = text.toString
        val header = check_thy_text(name, string)
        val more_uses = find_files(syntax, string)
        header.copy(uses = header.uses ::: more_uses.map((_, false)))
      })
}

