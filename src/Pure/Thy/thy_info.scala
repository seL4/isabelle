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
    val empty = new Dependencies(Nil, Set.empty)
  }

  final class Dependencies private(
    rev_deps: List[Dep],
    val seen: Set[Document.Node.Name])
  {
    def :: (dep: Dep): Dependencies = new Dependencies(dep :: rev_deps, seen)
    def + (name: Document.Node.Name): Dependencies = new Dependencies(rev_deps, seen = seen + name)

    def deps: List[Dep] = rev_deps.reverse

    def thy_load_commands: List[String] =
      (for ((_, h) <- rev_deps; (cmd, Some(((Keyword.THY_LOAD, _), _))) <- h.keywords) yield cmd) :::
        thy_load.base_syntax.thy_load_commands

    def loaded_theories: Set[String] =
      (thy_load.loaded_theories /: rev_deps) { case (loaded, (name, _)) => loaded + name.theory }

    def syntax: Outer_Syntax =
      (thy_load.base_syntax /: rev_deps) { case (syn, (name, h)) =>
        val syn1 = syn.add_keywords(h)
        // FIXME avoid hardwired stuff!?
        // FIXME broken?!
        if (name.theory == "Pure")
          syn1 +
            ("hence", (Keyword.PRF_ASM_GOAL, Nil), "then have") +
            ("thus", (Keyword.PRF_ASM_GOAL, Nil), "then show")
        else syn1
      }
  }

  private def require_thys(initiators: List[Document.Node.Name],
      required: Dependencies, names: List[Document.Node.Name]): Dependencies =
    (required /: names)(require_thy(initiators, _, _))

  private def require_thy(initiators: List[Document.Node.Name],
      required: Dependencies, name: Document.Node.Name): Dependencies =
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

  def dependencies(names: List[Document.Node.Name]): Dependencies =
    require_thys(Nil, Dependencies.empty, names)
}
