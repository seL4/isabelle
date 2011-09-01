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
        case XML.Elem(Markup(Markup.LOADED_THEORY, List((Markup.NAME, name))), _) => Some(name)
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

  def import_name(master_dir: String, str: String): Document.Node.Name =
  {
    val path = Path.explode(str)
    val node_name = thy_load.append(master_dir, Thy_Header.thy_path(path))
    val master_dir1 = thy_load.append(master_dir, path.dir)
    Document.Node.Name(node_name, master_dir1, path.base.implode)
  }

  type Deps = Map[Document.Node.Name, Document.Node_Header]

  private def require_thys(initiators: List[Document.Node.Name],
      deps: Deps, names: List[Document.Node.Name]): Deps =
    (deps /: names)(require_thy(initiators, _, _))

  private def require_thy(initiators: List[Document.Node.Name],
      deps: Deps, name: Document.Node.Name): Deps =
  {
    if (deps.isDefinedAt(name) || thy_load.is_loaded(name.theory)) deps
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
        val imports = header.imports.map(import_name(name.master_dir, _))
        require_thys(name :: initiators, deps + (name -> Exn.Res(header)), imports)
      }
      catch { case e: Throwable => deps + (name -> Exn.Exn(e)) }
    }
  }

  def dependencies(names: List[Document.Node.Name]): Deps =
    require_thys(Nil, Map.empty, names)
}
