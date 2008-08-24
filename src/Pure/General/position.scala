/*  Title:      Pure/General/position.scala
    ID:         $Id$
    Author:     Makarius

Position properties.
*/

package isabelle

import java.util.Properties


object Position {

  private def get_string(name: String, props: Properties) = {
    val value = if (props != null) props.getProperty(name) else null
    if (value != null) Some(value) else None
  }

  private def get_int(name: String, props: Properties) = {
    get_string(name, props) match {
      case None => None
      case Some(value) =>
        try { Some(Integer.parseInt(value)) }
        catch { case e: NumberFormatException => None }
    }
  }

  def line_of(props: Properties) = get_int(Markup.LINE, props)
  def column_of(props: Properties) = get_int(Markup.COLUMN, props)
  def offset_of(props: Properties) = get_int(Markup.OFFSET, props)
  def end_line_of(props: Properties) = get_int(Markup.END_LINE, props)
  def end_column_of(props: Properties) = get_int(Markup.END_COLUMN, props)
  def end_offset_of(props: Properties) = get_int(Markup.END_OFFSET, props)
  def file_of(props: Properties) = get_string(Markup.FILE, props)
  def id_of(props: Properties) = get_string(Markup.ID, props)
}
