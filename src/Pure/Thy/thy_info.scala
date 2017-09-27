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
    val empty = new Dependencies(Nil, Nil, Nil, Set.empty, Multi_Map.empty)
  }

  final class Dependencies private(
    rev_deps: List[Thy_Info.Dep],
    val keywords: Thy_Header.Keywords,
    val abbrevs: Thy_Header.Abbrevs,
    val seen: Set[Document.Node.Name],
    val seen_theory: Multi_Map[String, (Document.Node.Name, Position.T)])
  {
    def :: (dep: Thy_Info.Dep): Dependencies =
      new Dependencies(
        dep :: rev_deps, dep.header.keywords ::: keywords, dep.header.abbrevs ::: abbrevs,
        seen, seen_theory)

    def + (thy: (Document.Node.Name, Position.T)): Dependencies =
    {
      val (name, _) = thy
      new Dependencies(rev_deps, keywords, abbrevs, seen + name, seen_theory + (name.theory -> thy))
    }

    def deps: List[Thy_Info.Dep] = rev_deps.reverse

    def errors: List[String] =
    {
      val header_errors = deps.flatMap(dep => dep.header.errors)
      val import_errors =
        (for {
          (theory, imports) <- seen_theory.iterator_list
          if !resources.session_base.loaded_theories.isDefinedAt(theory)
          if imports.length > 1
        } yield {
          "Incoherent imports for theory " + quote(theory) + ":\n" +
            cat_lines(imports.map({ case (name, pos) =>
              "  " + quote(name.node) + Position.here(pos) }))
        }).toList
      header_errors ::: import_errors
    }

    lazy val syntax: Outer_Syntax =
      resources.session_base.syntax.add_keywords(keywords).add_abbrevs(abbrevs)

    def loaded_theories: Map[String, String] =
      (resources.session_base.loaded_theories /: rev_deps) {
        case (loaded, dep) =>
          val name = dep.name
          loaded + (name.theory -> name.theory) +
            (name.theory_base_name -> name.theory)  // legacy
      }

    def loaded_files: List[Path] =
    {
      val parses = rev_deps.map(dep => resources.loaded_files(syntax, dep.name))
      val dep_files = Par_List.map((parse: () => List[Path]) => parse(), parses)
      ((Nil: List[Path]) /: dep_files) { case (acc_files, files) => files ::: acc_files }
    }

    override def toString: String = deps.toString
  }

  private def require_thys(initiators: List[Document.Node.Name], required: Dependencies,
      thys: List[(Document.Node.Name, Position.T)]): Dependencies =
    (required /: thys)(require_thy(initiators, _, _))

  private def require_thy(initiators: List[Document.Node.Name], required: Dependencies,
    thy: (Document.Node.Name, Position.T)): Dependencies =
  {
    val (name, require_pos) = thy

    def message: String =
      "The error(s) above occurred for theory " + quote(name.theory) +
        required_by(initiators) + Position.here(require_pos)

    val required1 = required + thy
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
