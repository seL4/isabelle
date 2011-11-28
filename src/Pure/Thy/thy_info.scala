/*  Title:      Pure/Thy/thy_info.scala
    Author:     Makarius

Theory and file dependencies.
*/

package isabelle


object Thy_Info
{
  /* protocol messages */

  object Loaded_Theory {
    def unapply(msg: XML.Tree): Option[String] =
      msg match {
        case XML.Elem(Markup(Isabelle_Markup.LOADED_THEORY, List((Markup.NAME, name))), _) =>
          Some(name)
        case _ => None
      }
  }
}


class Thy_Info(thy_load: Thy_Load)
{
  /* messages */

  private def show_path(names: List[Document.Node.Name]): String =
    names.map(name => quote(name.theory)).mkString(" via ")

  private def cycle_msg(names: List[Document.Node.Name]): String =
    "Cyclic dependency of " + show_path(names)

  private def required_by(initiators: List[Document.Node.Name]): String =
    if (initiators.isEmpty) ""
    else "\n(required by " + show_path(initiators.reverse) + ")"


  /* dependencies */

  def import_name(dir: String, str: String): Document.Node.Name =
  {
    val path = Path.explode(str)
    val node = thy_load.append(dir, Thy_Header.thy_path(path))
    val dir1 = thy_load.append(dir, path.dir)
    val theory = path.base.implode
    Document.Node.Name(node, dir1, theory)
  }

  type Dep = (Document.Node.Name, Document.Node_Header)
  private type Required = (List[Dep], Set[Document.Node.Name])

  private def require_thys(initiators: List[Document.Node.Name],
      required: Required, names: List[Document.Node.Name]): Required =
    (required /: names)(require_thy(initiators, _, _))

  private def require_thy(initiators: List[Document.Node.Name],
      required: Required, name: Document.Node.Name): Required =
  {
    val (deps, seen) = required
    if (seen(name)) required
    else if (thy_load.is_loaded(name.theory)) (deps, seen + name)
    else {
      try {
        if (initiators.contains(name)) error(cycle_msg(initiators))
        val header =
          try { thy_load.check_thy(name) }
          catch {
            case ERROR(msg) =>
              cat_error(msg, "The error(s) above occurred while examining theory " +
                quote(name.theory) + required_by(initiators))
          }
        val imports = header.imports.map(import_name(name.dir, _))
        val (deps1, seen1) = require_thys(name :: initiators, (deps, seen + name), imports)
        ((name, Exn.Res(header)) :: deps1, seen1)
      }
      catch { case e: Throwable => (((name, Exn.Exn(e)): Dep) :: deps, seen + name) }
    }
  }

  def dependencies(names: List[Document.Node.Name]): List[Dep] =
    require_thys(Nil, (Nil, Set.empty), names)._1.reverse
}
