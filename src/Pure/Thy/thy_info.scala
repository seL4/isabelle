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
    val empty = new Dependencies(Nil, Nil, Multi_Map.empty, Multi_Map.empty)
  }

  final class Dependencies private(
    rev_deps: List[Dep],
    val keywords: Thy_Header.Keywords,
    val seen_names: Multi_Map[String, Document.Node.Name],
    val seen_positions: Multi_Map[String, Position.T])
  {
    def :: (dep: Dep): Dependencies =
      new Dependencies(dep :: rev_deps, dep.header.keywords ::: keywords,
        seen_names, seen_positions)

    def + (thy: (Document.Node.Name, Position.T)): Dependencies =
    {
      val (name, pos) = thy
      new Dependencies(rev_deps, keywords,
        seen_names + (name.theory -> name),
        seen_positions + (name.theory -> pos))
    }

    def deps: List[Dep] = rev_deps.reverse

    def errors: List[String] =
    {
      val header_errors = deps.flatMap(dep => dep.header.errors)
      val import_errors =
        (for {
          (theory, names) <- seen_names.iterator_list
          if !thy_load.loaded_theories(theory)
          if names.length > 1
        } yield
          "Incoherent imports for theory " + quote(theory) + ":\n" +
            cat_lines(names.flatMap(name =>
              seen_positions.get_list(theory).map(pos =>
                "  " + quote(name.node) + Position.here(pos))))
        ).toList
      header_errors ::: import_errors
    }

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
      required: Dependencies, thys: List[(Document.Node.Name, Position.T)]): Dependencies =
    (required /: thys)(require_thy(initiators, _, _))

  private def require_thy(initiators: List[Document.Node.Name],
      required: Dependencies, thy: (Document.Node.Name, Position.T)): Dependencies =
  {
    val (name, require_pos) = thy
    val theory = name.theory

    def message: String =
      "The error(s) above occurred for theory " + quote(theory) +
        required_by(initiators) + Position.here(require_pos)

    val required1 = required + thy
    if (required.seen_names.isDefinedAt(theory) || thy_load.loaded_theories(theory))
      required1
    else {
      try {
        if (initiators.contains(name)) error(cycle_msg(initiators))
        val header =
          try { thy_load.check_thy(name).cat_errors(message) }
          catch { case ERROR(msg) => cat_error(msg, message) }
        val imports = header.imports.map((_, Position.File(name.node)))
        Dep(name, header) :: require_thys(name :: initiators, required1, imports)
      }
      catch {
        case e: Throwable =>
          Dep(name, Document.Node.bad_header(Exn.message(e))) :: required1
      }
    }
  }

  def dependencies(thys: List[(Document.Node.Name, Position.T)]): Dependencies =
    require_thys(Nil, Dependencies.empty, thys)
}
