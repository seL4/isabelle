/*  Title:      Pure/Thy/thy_info.scala
    Author:     Makarius

Theory and file dependencies.
*/

package isabelle


object Thy_Info
{
  /* dependencies */

  sealed case class Dep(
    name: Document.Node.Name,
    header: Document.Node.Header)
  {
    override def toString: String = name.toString
  }
}

class Thy_Info(resources: Resources)
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

  object Dependencies
  {
    val empty = new Dependencies(Nil, Nil, Nil, Set.empty)
  }

  final class Dependencies private(
    rev_deps: List[Thy_Info.Dep],
    val keywords: Thy_Header.Keywords,
    val abbrevs: Thy_Header.Abbrevs,
    val seen: Set[Document.Node.Name])
  {
    def :: (dep: Thy_Info.Dep): Dependencies =
      new Dependencies(
        dep :: rev_deps, dep.header.keywords ::: keywords, dep.header.abbrevs ::: abbrevs, seen)

    def + (name: Document.Node.Name): Dependencies =
      new Dependencies(rev_deps, keywords, abbrevs, seen + name)

    def deps: List[Thy_Info.Dep] = rev_deps.reverse

    def errors: List[String] = deps.flatMap(dep => dep.header.errors)

    lazy val syntax: Outer_Syntax =
      resources.session_base.syntax.add_keywords(keywords).add_abbrevs(abbrevs)

    def loaded_theories: Set[String] =
      resources.session_base.loaded_theories ++ rev_deps.map(dep => dep.name.theory)

    def loaded_files: List[(String, List[Path])] =
    {
      val names = deps.map(_.name)
      names.map(_.theory) zip
        Par_List.map((e: () => List[Path]) => e(), names.map(resources.loaded_files(syntax, _)))
    }

    override def toString: String = deps.toString
  }

  private def require_thys(initiators: List[Document.Node.Name], required: Dependencies,
      thys: List[(Document.Node.Name, Position.T)]): Dependencies =
    (required /: thys)(require_thy(initiators, _, _))

  private def require_thy(initiators: List[Document.Node.Name], required: Dependencies,
    thy: (Document.Node.Name, Position.T)): Dependencies =
  {
    val (name, pos) = thy

    def message: String =
      "The error(s) above occurred for theory " + quote(name.theory) +
        required_by(initiators) + Position.here(pos)

    val required1 = required + name
    if (required.seen(name)) required
    else if (resources.session_base.loaded_theory(name)) required1
    else {
      try {
        if (initiators.contains(name)) error(cycle_msg(initiators))
        val header =
          try { resources.check_thy(name, Token.Pos.file(name.node)).cat_errors(message) }
          catch { case ERROR(msg) => cat_error(msg, message) }
        Thy_Info.Dep(name, header) :: require_thys(name :: initiators, required1, header.imports)
      }
      catch {
        case e: Throwable =>
          Thy_Info.Dep(name, Document.Node.bad_header(Exn.message(e))) :: required1
      }
    }
  }

  def dependencies(thys: List[(Document.Node.Name, Position.T)]): Dependencies =
    require_thys(Nil, Dependencies.empty, thys)
}
