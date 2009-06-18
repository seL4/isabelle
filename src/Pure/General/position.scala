/*  Title:      Pure/General/position.scala
    Author:     Makarius

Position properties.
*/

package isabelle

import java.util.Properties


object Position {

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

  def line_of(pos: T) = get_int(Markup.LINE, pos)
  def column_of(pos: T) = get_int(Markup.COLUMN, pos)
  def offset_of(pos: T) = get_int(Markup.OFFSET, pos)
  def end_line_of(pos: T) = get_int(Markup.END_LINE, pos)
  def end_column_of(pos: T) = get_int(Markup.END_COLUMN, pos)
  def end_offset_of(pos: T) = get_int(Markup.END_OFFSET, pos)
  def file_of(pos: T) = get_string(Markup.FILE, pos)
  def id_of(pos: T) = get_string(Markup.ID, pos)

  def offsets_of(pos: T): (Option[Int], Option[Int]) =
  {
    val begin = offset_of(pos)
    val end = end_offset_of(pos)
    (begin, if (end.isDefined) end else begin.map(_ + 1))
  }

}
