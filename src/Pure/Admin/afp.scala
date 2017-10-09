/*  Title:      Pure/Admin/afp.scala
    Author:     Makarius

Administrative support for the Archive of Formal Proofs.
*/

package isabelle


object AFP
{
  sealed case class Entry(name: String, sessions: List[String])

  def init(base_dir: Path = Path.explode("$AFP_BASE")): AFP = new AFP(base_dir)
}

class AFP private(val base_dir: Path)
{
  val main_dir: Path = base_dir + Path.explode("thys")

  val entries: List[AFP.Entry] =
    (for (name <- Sessions.parse_roots(main_dir + Sessions.ROOTS))
    yield {
      val sessions =
        Sessions.parse_root_entries(main_dir + Path.explode(name) + Sessions.ROOT).map(_.name)
      AFP.Entry(name, sessions)
    }).sortBy(_.name)

  val sessions: List[String] = entries.flatMap(_.sessions).sorted

  override def toString: String = base_dir.expand.toString
}
