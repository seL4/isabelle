/*  Title:      Pure/PIDE/text.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Basic operations on plain text.
*/

package isabelle


object Text
{
  /* offset */

  type Offset = Int


  /* range -- with total quasi-ordering */

  object Range
  {
    def apply(start: Offset): Range = Range(start, start)
  }

  sealed case class Range(val start: Offset, val stop: Offset)
  {
    // denotation: {start} Un {i. start < i & i < stop}
    require(start <= stop)

    override def toString = "[" + start.toString + ":" + stop.toString + "]"

    def map(f: Offset => Offset): Range = Range(f(start), f(stop))
    def +(i: Offset): Range = map(_ + i)
    def -(i: Offset): Range = map(_ - i)
    def contains(i: Offset): Boolean = start == i || start < i && i < stop
    def contains(that: Range): Boolean = this.contains(that.start) && that.stop <= this.stop
    def overlaps(that: Range): Boolean = this.contains(that.start) || that.contains(this.start)
    def compare(that: Range): Int = if (overlaps(that)) 0 else this.start compare that.start

    def restrict(that: Range): Range =
      Range(this.start max that.start, this.stop min that.stop)
  }


  /* information associated with text range */

  case class Info[A](val range: Text.Range, val info: A)
  {
    def restrict(r: Text.Range): Info[A] = Info(range.restrict(r), info)
  }


  /* editing */

  object Edit
  {
    def insert(start: Offset, text: String): Edit = new Edit(true, start, text)
    def remove(start: Offset, text: String): Edit = new Edit(false, start, text)
  }

  class Edit(val is_insert: Boolean, val start: Offset, val text: String)
  {
    override def toString =
      (if (is_insert) "Insert(" else "Remove(") + (start, text).toString + ")"


    /* transform offsets */

    private def transform(do_insert: Boolean, i: Offset): Offset =
      if (i < start) i
      else if (is_insert == do_insert) i + text.length
      else (i - text.length) max start

    def convert(i: Offset): Offset = transform(true, i)
    def revert(i: Offset): Offset = transform(false, i)


    /* edit strings */

    private def insert(i: Offset, string: String): String =
      string.substring(0, i) + text + string.substring(i)

    private def remove(i: Offset, count: Int, string: String): String =
      string.substring(0, i) + string.substring(i + count)

    def can_edit(string: String, shift: Int): Boolean =
      shift <= start && start < shift + string.length

    def edit(string: String, shift: Int): (Option[Edit], String) =
      if (!can_edit(string, shift)) (Some(this), string)
      else if (is_insert) (None, insert(start - shift, string))
      else {
        val i = start - shift
        val count = text.length min (string.length - i)
        val rest =
          if (count == text.length) None
          else Some(Edit.remove(start, text.substring(count)))
        (rest, remove(i, count, string))
      }
  }
}
