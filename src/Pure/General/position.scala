/*  Title:      Pure/General/position.scala
    Author:     Makarius

Position properties.
*/

package isabelle


import java.io.{File => JFile}


object Position
{
  type T = Properties.T

  val Line = new Properties.Int(Isabelle_Markup.LINE)
  val Offset = new Properties.Int(Isabelle_Markup.OFFSET)
  val End_Offset = new Properties.Int(Isabelle_Markup.END_OFFSET)
  val File = new Properties.String(Isabelle_Markup.FILE)
  val Id = new Properties.Long(Isabelle_Markup.ID)

  object Line_File
  {
    def unapply(pos: T): Option[(Int, String)] =
      (pos, pos) match {
        case (Line(i), File(name)) => Some((i, name))
        case (_, File(name)) => Some((1, name))
        case _ => None
      }
  }

  object Range
  {
    def apply(range: Text.Range): T = Offset(range.start) ++ Offset(range.stop)
    def unapply(pos: T): Option[Text.Range] =
      (pos, pos) match {
        case (Offset(start), End_Offset(stop)) if start <= stop => Some(Text.Range(start, stop))
        case (Offset(start), _) => Some(Text.Range(start, start + 1))
        case _ => None
      }
  }

  object Id_Offset
  {
    def unapply(pos: T): Option[(Long, Text.Offset)] =
      (pos, pos) match {
        case (Id(id), Offset(offset)) => Some((id, offset))
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


  def str_of(pos: T): String =
    (Line.unapply(pos), File.unapply(pos)) match {
      case (Some(i), None) => " (line " + i.toString + ")"
      case (Some(i), Some(name)) => " (line " + i.toString + " of " + quote(name) + ")"
      case (None, Some(name)) => " (file " + quote(name) + ")"
      case _ => ""
    }
}
