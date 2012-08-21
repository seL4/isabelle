/*  Title:      Pure/Thy/thy_info.scala
    Author:     Makarius

Theory and file dependencies.
*/

package isabelle


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

  type Dep = (Document.Node.Name, Document.Node.Header)
  private sealed case class Required(
    deps: List[Dep] = Nil,
    seen: Set[Document.Node.Name] = Set.empty)
  {
    def :: (dep: Dep): Required = copy(deps = dep :: deps)
    def + (name: Document.Node.Name): Required = copy(seen = seen + name)
  }

  private def require_thys(initiators: List[Document.Node.Name],
      required: Required, names: List[Document.Node.Name]): Required =
    (required /: names)(require_thy(initiators, _, _))

  private def require_thy(initiators: List[Document.Node.Name],
      required: Required, name: Document.Node.Name): Required =
  {
    if (required.seen(name)) required
    else if (thy_load.loaded_theories(name.theory)) required + name
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
        (name, header) :: require_thys(name :: initiators, required + name, header.imports)
      }
      catch {
        case e: Throwable =>
          (name, Document.Node.bad_header(Exn.message(e))) :: (required + name)
      }
    }
  }

  def dependencies(names: List[Document.Node.Name]): List[Dep] =
    require_thys(Nil, Required(), names).deps.reverse
}
