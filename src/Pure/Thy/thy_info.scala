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
    header0: Document.Node.Header,
    future_header: JFuture[Exn.Result[Document.Node.Header]])
  {
    def join_header: Document.Node.Header = Exn.release(future_header.get)
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
      new Dependencies(dep :: rev_deps, dep.header0.keywords ::: keywords, seen)

    def + (name: Document.Node.Name): Dependencies =
      new Dependencies(rev_deps, keywords, seen = seen + name)

    def deps: List[Dep] = rev_deps.reverse

    def loaded_theories: Set[String] =
      (thy_load.loaded_theories /: rev_deps) { case (loaded, dep) => loaded + dep.name.theory }

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
      def err(msg: String): Nothing =
        cat_error(msg, "The error(s) above occurred while examining theory " +
          quote(name.theory) + required_by(initiators))

      try {
        if (initiators.contains(name)) error(cycle_msg(initiators))
        val syntax = required.make_syntax

        val header0 =
          try { thy_load.check_thy(name) }
          catch { case ERROR(msg) => err(msg) }

        val future_header: JFuture[Exn.Result[Document.Node.Header]] =
          if (files) {
            val string = thy_load.with_thy_text(name, _.toString)
            val syntax0 = syntax.add_keywords(header0.keywords)

            if (thy_load.body_files_test(syntax0, string)) {
              /* FIXME
                  unstable in scala-2.9.2 on multicore hardware -- spurious NPE
                  OK in scala-2.10.0.RC3 */
              // default_thread_pool.submit(() =>
                Library.future_value(Exn.capture {
                  try {
                    val files = thy_load.body_files(syntax0, string)
                    header0.copy(uses = header0.uses ::: files.map((_, false)))
                  }
                  catch { case ERROR(msg) => err(msg) }
                })
              //)
            }
            else Library.future_value(Exn.Res(header0))
          }
          else Library.future_value(Exn.Res(header0))

        Dep(name, header0, future_header) ::
          require_thys(files, name :: initiators, required + name, header0.imports)
      }
      catch {
        case e: Throwable =>
          val bad_header = Document.Node.bad_header(Exn.message(e))
          Dep(name, bad_header, Library.future_value(Exn.Res(bad_header))) :: (required + name)
      }
    }
  }

  def dependencies(inlined_files: Boolean, names: List[Document.Node.Name]): Dependencies =
    require_thys(inlined_files, Nil, Dependencies.empty, names)
}
