/*  Title:      Pure/General/position.scala
    Author:     Makarius

Position properties.
*/

package isabelle


object Position
{
  type T = List[(String, String)]

  private def get_string(name: String, pos: T): Option[String] =
    pos.find(p => p._1 == name).map(_._2)

  private def get_int(name: String, pos: T): Option[Int] =
  {
    get_string(name, pos) match {
      case None => None
      case Some(value) =>
        try { Some(Integer.parseInt(value)) }
        catch { case _: NumberFormatException => None }
    }
  }

  def get_line(pos: T): Option[Int] = get_int(Markup.LINE, pos)
  def get_column(pos: T): Option[Int] = get_int(Markup.COLUMN, pos)
  def get_offset(pos: T): Option[Int] = get_int(Markup.OFFSET, pos)
  def get_end_line(pos: T): Option[Int] = get_int(Markup.END_LINE, pos)
  def get_end_column(pos: T): Option[Int] = get_int(Markup.END_COLUMN, pos)
  def get_end_offset(pos: T): Option[Int] = get_int(Markup.END_OFFSET, pos)
  def get_file(pos: T): Option[String] = get_string(Markup.FILE, pos)
  def get_id(pos: T): Option[String] = get_string(Markup.ID, pos)

  def get_offsets(pos: T): (Option[Int], Option[Int]) =
  {
    val begin = get_offset(pos)
    val end = get_end_offset(pos)
    (begin, if (end.isDefined) end else begin.map(_ + 1))
  }
}
