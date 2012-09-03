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

  object Dependencies
  {
    val empty = new Dependencies(Nil, Nil, Set.empty)
  }

  final class Dependencies private(
    rev_deps: List[Dep],
    val keywords: Thy_Header.Keywords,
    val seen: Set[Document.Node.Name])
  {
    def :: (dep: Dep): Dependencies =
      new Dependencies(dep :: rev_deps, dep._2.keywords ::: keywords, seen)

    def + (name: Document.Node.Name): Dependencies =
      new Dependencies(rev_deps, keywords, seen = seen + name)

    def deps: List[Dep] = rev_deps.reverse

    def loaded_theories: Set[String] =
      (thy_load.loaded_theories /: rev_deps) { case (loaded, (name, _)) => loaded + name.theory }

    def make_syntax: Outer_Syntax = thy_load.base_syntax.add_keywords(keywords)
  }

  private def require_thys(files: Boolean, initiators: List[Document.Node.Name],
      required: Dependencies, names: List[Document.Node.Name]): Dependencies =
    (required /: names)(require_thy(files, initiators, _, _))

  private def require_thy(files: Boolean, initiators: List[Document.Node.Name],
      required: Dependencies, name: Document.Node.Name): Dependencies =
  {
    if (required.seen(name)) required
    else if (thy_load.loaded_theories(name.theory)) required + name
    else {
      try {
        if (initiators.contains(name)) error(cycle_msg(initiators))
        val syntax = required.make_syntax
        val header =
          try {
            if (files) thy_load.check_thy_files(syntax, name)
            else thy_load.check_thy(name)
          }
          catch {
            case ERROR(msg) =>
              cat_error(msg, "The error(s) above occurred while examining theory " +
                quote(name.theory) + required_by(initiators))
          }
        (name, header) :: require_thys(files, name :: initiators, required + name, header.imports)
      }
      catch {
        case e: Throwable =>
          (name, Document.Node.bad_header(Exn.message(e))) :: (required + name)
      }
    }
  }

  def dependencies(inlined_files: Boolean, names: List[Document.Node.Name]): Dependencies =
    require_thys(inlined_files, Nil, Dependencies.empty, names)
}
