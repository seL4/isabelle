/*  Title:      Pure/Thy/thy_info.scala
    Author:     Makarius

Theory and file dependencies.
*/

package isabelle


class Thy_Info(thy_load: Thy_Load)
{
  /* messages */

  private def show_path(names: List[String]): String =
    names.map(Library.quote).mkString(" via ")

  private def cycle_msg(names: List[String]): String =
    "Cyclic dependency of " + show_path(names)

  private def required_by(s: String, initiators: List[String]): String =
    if (initiators.isEmpty) ""
    else s + "(required by " + show_path(initiators.reverse) + ")"


  /* dependencies */

  type Deps = Map[String, Exn.Result[(String, Thy_Header.Header)]]  // name -> (text, header)

  private def require_thys(
      initiators: List[String], dir: Path, deps: Deps, strs: List[String]): Deps =
    (deps /: strs)(require_thy(initiators, dir, _, _))

  private def require_thy(initiators: List[String], dir: Path, deps: Deps, str: String): Deps =
  {
    val path = Path.explode(str)
    val name = path.base.implode

    if (deps.isDefinedAt(name)) deps
    else {
      val dir1 = dir + path.dir
      try {
        if (initiators.contains(name)) error(cycle_msg(initiators))
        val (text, header) =
          try { thy_load.check_thy(dir1, name) }
          catch {
            case ERROR(msg) =>
              cat_error(msg, "The error(s) above occurred while examining theory " +
                Library.quote(name) + required_by("\n", initiators))
          }
        require_thys(name :: initiators, dir1,
          deps + (name -> Exn.Res(text, header)), header.imports)
      }
      catch { case e: Throwable => deps + (name -> Exn.Exn(e)) }
    }
  }

  def dependencies(dir: Path, str: String): Deps =
    require_thy(Nil, dir, Map.empty, str)  // FIXME capture errors in str (!??)
}
