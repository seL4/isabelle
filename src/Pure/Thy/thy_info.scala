/*  Title:      Pure/Thy/thy_info.scala
    Author:     Makarius

Theory and file dependencies.
*/

package isabelle


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
    rev_entries: List[Document.Node.Entry],
    val keywords: Thy_Header.Keywords,
    val abbrevs: Thy_Header.Abbrevs,
    val seen: Set[Document.Node.Name])
  {
    def :: (entry: Document.Node.Entry): Dependencies =
      new Dependencies(
        entry :: rev_entries,
        entry.header.keywords ::: keywords,
        entry.header.abbrevs ::: abbrevs,
        seen)

    def + (name: Document.Node.Name): Dependencies =
      new Dependencies(rev_entries, keywords, abbrevs, seen + name)

    def entries: List[Document.Node.Entry] = rev_entries.reverse
    def names: List[Document.Node.Name] = entries.map(_.name)

    def errors: List[String] = entries.flatMap(_.header.errors)

    lazy val syntax: Outer_Syntax =
      resources.session_base.syntax.add_keywords(keywords).add_abbrevs(abbrevs)

    def loaded_theories: Set[String] =
      resources.session_base.loaded_theories ++ rev_entries.map(_.name.theory)

    def loaded_files: List[(String, List[Path])] =
    {
      names.map(_.theory) zip
        Par_List.map((e: () => List[Path]) => e(), names.map(resources.loaded_files(syntax, _)))
    }

    override def toString: String = entries.toString
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
        Document.Node.Entry(name, header) ::
          require_thys(name :: initiators, required1, header.imports)
      }
      catch {
        case e: Throwable =>
          Document.Node.Entry(name, Document.Node.bad_header(Exn.message(e))) :: required1
      }
    }
  }

  def dependencies(thys: List[(Document.Node.Name, Position.T)]): Dependencies =
    require_thys(Nil, Dependencies.empty, thys)
}
