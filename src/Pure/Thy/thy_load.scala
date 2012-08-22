/*  Title:      Pure/Thy/thy_load.scala
    Author:     Makarius

Primitives for loading theory files.
*/

package isabelle


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

  def check_thy_text(name: Document.Node.Name, text: CharSequence): Document.Node.Header =
  {
    val header = Thy_Header.read(text)
    val name1 = header.name
    val imports = header.imports.map(import_name(name.dir, _))
    // FIXME val uses = header.uses.map(p => (append(name.dir, Path.explode(p._1)), p._2))
    val uses = header.uses
    if (name.theory != name1)
      error("Bad file name " + Thy_Load.thy_path(Path.basic(name.theory)) +
        " for theory " + quote(name1))
    Document.Node.Header(imports, header.keywords, uses)
  }

  def check_thy(name: Document.Node.Name): Document.Node.Header =
  {
    val path = Path.explode(name.node)
    if (!path.is_file) error("No such file: " + path.toString)
    check_thy_text(name, File.read(path))
  }
}

