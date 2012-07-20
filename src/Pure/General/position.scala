/*  Title:      Pure/General/position.scala
    Author:     Makarius

Position properties.
*/

package isabelle


object Position
{
  type T = Properties.T

  val Line = new Properties.Int(Isabelle_Markup.LINE)
  val Offset = new Properties.Int(Isabelle_Markup.OFFSET)
  val End_Offset = new Properties.Int(Isabelle_Markup.END_OFFSET)
  val File = new Properties.String(Isabelle_Markup.FILE)
  val Id = new Properties.Long(Isabelle_Markup.ID)

  def file(f: java.io.File): T = File(Isabelle_System.posix_path(f.toString))
  def line_file(i: Int, f: java.io.File): T = Line(i) ::: file(f)

  object Range
  {
    def apply(range: Text.Range): T = Offset(range.start) ++ Offset(range.stop)
    def unapply(pos: T): Option[Text.Range] =
      (Offset.unapply(pos), End_Offset.unapply(pos)) match {
        case (Some(start), Some(stop)) if start <= stop => Some(Text.Range(start, stop))
        case (Some(start), None) => Some(Text.Range(start, start + 1))
        case _ => None
      }
  }

  object Id_Range
  {
    def unapply(pos: T): Option[(Long, Text.Range)] =
      (pos, pos) match {
        case (Id(id), Range(range)) => Some((id, range))
        case _ => None
      }
  }

  private val purge_pos = Map(
    Isabelle_Markup.DEF_LINE -> Isabelle_Markup.LINE,
    Isabelle_Markup.DEF_OFFSET -> Isabelle_Markup.OFFSET,
    Isabelle_Markup.DEF_END_OFFSET -> Isabelle_Markup.END_OFFSET,
    Isabelle_Markup.DEF_FILE -> Isabelle_Markup.FILE,
    Isabelle_Markup.DEF_ID -> Isabelle_Markup.ID)

  def purge(props: T): T =
    for ((x, y) <- props if !Isabelle_Markup.POSITION_PROPERTIES(x))
      yield (if (purge_pos.isDefinedAt(x)) (purge_pos(x), y) else (x, y))


  def str_of(props: T): String =
    (Line.unapply(props), File.unapply(props)) match {
      case (Some(i), None) => " (line " + i.toString + ")"
      case (Some(i), Some(name)) => " (line " + i.toString + " of " + quote(name) + ")"
      case (None, Some(name)) => " (file " + quote(name) + ")"
      case _ => ""
    }
}
