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
  private type Required = (List[Dep], Set[Document.Node.Name])

  private def require_thys(initiators: List[Document.Node.Name],
      required: Required, names: List[Document.Node.Name]): Required =
    (required /: names)(require_thy(initiators, _, _))

  private def require_thy(initiators: List[Document.Node.Name],
      required: Required, name: Document.Node.Name): Required =
  {
    val (deps, seen) = required
    if (seen(name)) required
    else if (thy_load.loaded_theories(name.theory)) (deps, seen + name)
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
        val (deps1, seen1) =
          require_thys(name :: initiators, (deps, seen + name), header.imports)
        ((name, header) :: deps1, seen1)
      }
      catch {
        case e: Throwable =>
          ((name, Document.Node.bad_header(Exn.message(e))) :: deps, seen + name)
      }
    }
  }

  def dependencies(names: List[Document.Node.Name]): List[Dep] =
    require_thys(Nil, (Nil, Set.empty), names)._1.reverse
}
