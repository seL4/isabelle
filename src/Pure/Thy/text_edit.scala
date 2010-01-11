/*  Title:      Pure/Thy/text_edit.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Basic edits on plain text.
*/

package isabelle


class Text_Edit(val is_insert: Boolean, val start: Int, val text: String)
{
  override def toString =
    (if (is_insert) "Insert(" else "Remove(") + (start, text).toString + ")"


  /* transform offsets */

  private def transform(do_insert: Boolean, offset: Int): Int =
    if (offset < start) offset
    else if (is_insert == do_insert) offset + text.length
    else (offset - text.length) max start

  def after(offset: Int): Int = transform(true, offset)
  def before(offset: Int): Int = transform(false, offset)


  /* edit strings */

  private def insert(index: Int, string: String): String =
    string.substring(0, index) + text + string.substring(index)

  private def remove(index: Int, count: Int, string: String): String =
    string.substring(0, index) + string.substring(index + count)

  def can_edit(string: String, shift: Int): Boolean =
    shift <= start && start < shift + string.length

  def edit(string: String, shift: Int): (Option[Text_Edit], String) =
    if (!can_edit(string, shift)) (Some(this), string)
    else if (is_insert) (None, insert(start - shift, string))
    else {
      val index = start - shift
      val count = text.length min (string.length - index)
      val rest =
        if (count == text.length) None
        else Some(new Text_Edit(false, start, text.substring(count)))
      (rest, remove(index, count, string))
    }
}

