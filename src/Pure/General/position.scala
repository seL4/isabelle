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

  val Def_Line = new Properties.Int(Isabelle_Markup.DEF_LINE)
  val Def_Offset = new Properties.Int(Isabelle_Markup.DEF_OFFSET)
  val Def_End_Offset = new Properties.Int(Isabelle_Markup.DEF_END_OFFSET)
  val Def_File = new Properties.String(Isabelle_Markup.DEF_FILE)
  val Def_Id = new Properties.Long(Isabelle_Markup.DEF_ID)

  object Line_File
  {
    def unapply(pos: T): Option[(Int, String)] =
      (pos, pos) match {
        case (Line(i), File(name)) => Some((i, name))
        case (_, File(name)) => Some((1, name))
        case _ => None
      }
  }

  object Def_Line_File
  {
    def unapply(pos: T): Option[(Int, String)] =
      (pos, pos) match {
        case (Def_Line(i), Def_File(name)) => Some((i, name))
        case (_, Def_File(name)) => Some((1, name))
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

  object Def_Id_Offset
  {
    def unapply(pos: T): Option[(Long, Text.Offset)] =
      (pos, pos) match {
        case (Def_Id(id), Def_Offset(offset)) => Some((id, offset))
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

  def purge(props: T): T = props.filterNot(p => Isabelle_Markup.POSITION_PROPERTIES(p._1))


  /* here: inlined formal markup */

  def here(pos: T): String =
    (Line.unapply(pos), File.unapply(pos)) match {
      case (Some(i), None) => " (line " + i.toString + ")"
      case (Some(i), Some(name)) => " (line " + i.toString + " of " + quote(name) + ")"
      case (None, Some(name)) => " (file " + quote(name) + ")"
      case _ => ""
    }
}
