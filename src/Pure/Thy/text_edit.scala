/*  Title:      Pure/Thy/text_edit.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Basic edits on plain text.
*/

package isabelle


sealed abstract class Text_Edit
{
  val start: Int
  def text: String
  def after(offset: Int): Int
  def before(offset: Int): Int
  def can_edit(string_length: Int, shift: Int): Boolean
  def edit(string: String, shift: Int): (Option[Text_Edit], String)
}


object Text_Edit
{
  /* transform offsets */

  private def after_insert(start: Int, text: String, offset: Int): Int =
    if (start <= offset) offset + text.length
    else offset

  private def after_remove(start: Int, text: String, offset: Int): Int =
    if (start > offset) offset
    else (offset - text.length) max start


  /* edit strings */

  private def insert(index: Int, text: String, string: String): String =
    string.substring(0, index) + text + string.substring(index)

  private def remove(index: Int, count: Int, string: String): String =
    string.substring(0, index) + string.substring(index + count)


  /* explicit edits */

  case class Insert(start: Int, text: String) extends Text_Edit
  {
    def after(offset: Int): Int = after_insert(start, text, offset)
    def before(offset: Int): Int = after_remove(start, text, offset)

    def can_edit(string_length: Int, shift: Int): Boolean =
      shift <= start && start <= shift + string_length

    def edit(string: String, shift: Int): (Option[Insert], String) =
      if (can_edit(string.length, shift)) (None, insert(start - shift, text, string))
      else (Some(this), string)
  }

  case class Remove(start: Int, text: String) extends Text_Edit
  {
    def after(offset: Int): Int = after_remove(start, text, offset)
    def before(offset: Int): Int = after_insert(start, text, offset)

    def can_edit(string_length: Int, shift: Int): Boolean =
      shift <= start && start < shift + string_length

    def edit(string: String, shift: Int): (Option[Remove], String) =
      if (can_edit(string.length, shift)) {
        val index = start - shift
        val count = text.length min (string.length - index)
        val rest =
          if (count == text.length) None
          else Some(Remove(start, text.substring(count)))
        (rest, remove(index, count, string))
      }
      else (Some(this), string)
  }
}

