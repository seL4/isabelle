/*  Title:      Pure/Thy/text_edit.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Basic edits on plain text.
*/

package isabelle


sealed abstract class Text_Edit
{
  val start: Int
  def before(offset: Int): Int
  def after(offset: Int): Int
}


object Text_Edit
{
  case class Insert(start: Int, text: String) extends Text_Edit
  {
    def before(offset: Int): Int =
      if (start > offset) offset
      else (offset - text.length) max start

    def after(offset: Int): Int =
      if (start <= offset) offset + text.length
      else offset
  }

  case class Remove(start: Int, text: String) extends Text_Edit
  {
    def before(offset: Int): Int =
      if (start <= offset) offset + text.length
      else offset

    def after(offset: Int): Int =
      if (start > offset) offset
      else (offset - text.length) max start
  }
}

