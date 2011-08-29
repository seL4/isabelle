/*  Title:      Pure/Thy/thy_info.scala
    Author:     Makarius

Theory and file dependencies.
*/

package isabelle


object Thy_Info
{
  /* protocol messages */

  object Loaded_Theory {
    def unapply(msg: XML.Tree): Option[String] =
      msg match {
        case XML.Elem(Markup(Markup.LOADED_THEORY, List((Markup.NAME, name))), _) => Some(name)
        case _ => None
      }
  }
}


class Thy_Info(thy_load: Thy_Load)
{
  /* messages */

  private def show_path(names: List[String]): String =
    names.map(quote).mkString(" via ")

  private def cycle_msg(names: List[String]): String =
    "Cyclic dependency of " + show_path(names)

  private def required_by(s: String, initiators: List[String]): String =
    if (initiators.isEmpty) ""
    else s + "(required by " + show_path(initiators.reverse) + ")"


  /* dependencies */

  type Deps = Map[String, Document.Node_Header]

  private def require_thys(initiators: List[String],
      deps: Deps, thys: List[(String, String)]): Deps =
    (deps /: thys)(require_thy(initiators, _, _))

  private def require_thy(initiators: List[String], deps: Deps, thy: (String, String)): Deps =
  {
    val (dir, str) = thy
    val path = Path.explode(str)
    val thy_name = path.base.implode
    val node_name = thy_load.append(dir, Thy_Header.thy_path(path))

    if (deps.isDefinedAt(node_name) || thy_load.is_loaded(thy_name)) deps
    else {
      val dir1 = thy_load.append(dir, path.dir)
      try {
        if (initiators.contains(node_name)) error(cycle_msg(initiators))
        val header =
          try { thy_load.check_thy(node_name) }
          catch {
            case ERROR(msg) =>
              cat_error(msg, "The error(s) above occurred while examining theory file " +
                quote(node_name) + required_by("\n", initiators))
          }
        val thys = header.imports.map(str => (dir1, str))
        require_thys(node_name :: initiators, deps + (node_name -> Exn.Res(header)), thys)
      }
      catch { case e: Throwable => deps + (node_name -> Exn.Exn(e)) }
    }
  }

  def dependencies(thys: List[(String, String)]): Deps =
    require_thys(Nil, Map.empty, thys)
}
