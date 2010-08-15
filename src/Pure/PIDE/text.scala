/*  Title:      Pure/PIDE/text.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Basic operations on plain text.
*/

package isabelle


object Text
{
  /* edits */

  object Edit
  {
    def insert(start: Int, text: String): Edit = new Edit(true, start, text)
    def remove(start: Int, text: String): Edit = new Edit(false, start, text)
  }

  class Edit(val is_insert: Boolean, val start: Int, val text: String)
  {
    override def toString =
      (if (is_insert) "Insert(" else "Remove(") + (start, text).toString + ")"


    /* transform offsets */

    private def transform(do_insert: Boolean, offset: Int): Int =
      if (offset < start) offset
      else if (is_insert == do_insert) offset + text.length
      else (offset - text.length) max start

    def convert(offset: Int): Int = transform(true, offset)
    def revert(offset: Int): Int = transform(false, offset)


    /* edit strings */

    private def insert(index: Int, string: String): String =
      string.substring(0, index) + text + string.substring(index)

    private def remove(index: Int, count: Int, string: String): String =
      string.substring(0, index) + string.substring(index + count)

    def can_edit(string: String, shift: Int): Boolean =
      shift <= start && start < shift + string.length

    def edit(string: String, shift: Int): (Option[Edit], String) =
      if (!can_edit(string, shift)) (Some(this), string)
      else if (is_insert) (None, insert(start - shift, string))
      else {
        val index = start - shift
        val count = text.length min (string.length - index)
        val rest =
          if (count == text.length) None
          else Some(Edit.remove(start, text.substring(count)))
        (rest, remove(index, count, string))
      }
  }
}
