/*  Title:      Pure/General/position.scala
    Author:     Makarius

Position properties.
*/

package isabelle


object Position
{
  type T = Properties.T

  val Line = new Properties.Int(Markup.LINE)
  val Offset = new Properties.Int(Markup.OFFSET)
  val End_Offset = new Properties.Int(Markup.END_OFFSET)
  val File = new Properties.String(Markup.FILE)
  val Id = new Properties.Long(Markup.ID)

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
    Markup.DEF_LINE -> Markup.LINE,
    Markup.DEF_OFFSET -> Markup.OFFSET,
    Markup.DEF_END_OFFSET -> Markup.END_OFFSET,
    Markup.DEF_FILE -> Markup.FILE,
    Markup.DEF_ID -> Markup.ID)

  def purge(props: T): T =
    for ((x, y) <- props if !Markup.POSITION_PROPERTIES(x))
      yield (if (purge_pos.isDefinedAt(x)) (purge_pos(x), y) else (x, y))
}
