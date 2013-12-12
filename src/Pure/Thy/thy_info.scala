/*  Title:      Pure/Thy/thy_info.scala
    Author:     Makarius

Theory and file dependencies.
*/

package isabelle


import java.util.concurrent.{Future => JFuture}


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

  sealed case class Dep(
    name: Document.Node.Name,
    header: Document.Node.Header)
  {
    def load_files(syntax: Outer_Syntax): List[String] =
    {
      val string = thy_load.with_thy_text(name, _.toString)
      if (thy_load.body_files_test(syntax, string))
        thy_load.body_files(syntax, string)
      else Nil
    }
  }

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
      new Dependencies(dep :: rev_deps, dep.header.keywords ::: keywords, seen)

    def + (name: Document.Node.Name): Dependencies =
      new Dependencies(rev_deps, keywords, seen = seen + name)

    def deps: List[Dep] = rev_deps.reverse

    def errors: List[String] = deps.flatMap(dep => dep.header.errors)

    lazy val syntax: Outer_Syntax = thy_load.base_syntax.add_keywords(keywords)

    def loaded_theories: Set[String] =
      (thy_load.loaded_theories /: rev_deps) { case (loaded, dep) => loaded + dep.name.theory }

    def load_files: List[Path] =
    {
      val dep_files =
        rev_deps.par.map(dep =>
          Exn.capture {
            dep.load_files(syntax).map(a => Path.explode(dep.name.master_dir) + Path.explode(a))
          }).toList
      ((Nil: List[Path]) /: dep_files) {
        case (acc_files, files) => Exn.release(files) ::: acc_files
      }
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
      def message: String =
        "The error(s) above occurred for theory " + quote(name.theory) + required_by(initiators)

      try {
        if (initiators.contains(name)) error(cycle_msg(initiators))
        val header =
          try { thy_load.check_thy(name).cat_errors(message) }
          catch { case ERROR(msg) => cat_error(msg, message) }
        Dep(name, header) :: require_thys(name :: initiators, required + name, header.imports)
      }
      catch {
        case e: Throwable =>
          Dep(name, Document.Node.bad_header(Exn.message(e))) :: (required + name)
      }
    }
  }

  def dependencies(names: List[Document.Node.Name]): Dependencies =
    require_thys(Nil, Dependencies.empty, names)
}
