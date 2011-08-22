/*  Title:      Pure/PIDE/text.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Basic operations on plain text.
*/

package isabelle


import scala.collection.mutable
import scala.math.Ordering
import scala.util.Sorting


object Text
{
  /* offset */

  type Offset = Int


  /* range -- with total quasi-ordering */

  object Range
  {
    def apply(start: Offset): Range = Range(start, start)

    object Ordering extends scala.math.Ordering[Text.Range]
    {
      def compare(r1: Text.Range, r2: Text.Range): Int = r1 compare r2
    }
  }

  sealed case class Range(val start: Offset, val stop: Offset)
  {
    // denotation: {start} Un {i. start < i & i < stop}
    if (start > stop)
      error("Bad range: [" + start.toString + ":" + stop.toString + "]")

    override def toString = "[" + start.toString + ":" + stop.toString + "]"

    def map(f: Offset => Offset): Range = Range(f(start), f(stop))
    def +(i: Offset): Range = map(_ + i)
    def -(i: Offset): Range = map(_ - i)

    def is_singularity: Boolean = start == stop

    def contains(i: Offset): Boolean = start == i || start < i && i < stop
    def contains(that: Range): Boolean = this.contains(that.start) && that.stop <= this.stop
    def overlaps(that: Range): Boolean = this.contains(that.start) || that.contains(this.start)
    def compare(that: Range): Int = if (overlaps(that)) 0 else this.start compare that.start

    def restrict(that: Range): Range =
      Range(this.start max that.start, this.stop min that.stop)

    def try_restrict(that: Range): Option[Range] =
      try { Some (restrict(that)) }
      catch { case ERROR(_) => None }
  }


  /* perspective */

  type Perspective = List[Range]  // partitioning in canonical order

  def perspective(ranges: Seq[Range]): Perspective =
  {
    val sorted_ranges = ranges.toArray
    Sorting.quickSort(sorted_ranges)(Range.Ordering)

    val result = new mutable.ListBuffer[Text.Range]
    var last: Option[Text.Range] = None
    for (range <- sorted_ranges)
    {
      last match {
        case Some(last_range)
        if ((last_range overlaps range) || last_range.stop == range.start) =>
          last = Some(Text.Range(last_range.start, range.stop))
        case _ =>
          result ++= last
          last = Some(range)
      }
    }
    result ++= last
    result.toList
  }


  /* information associated with text range */

  sealed case class Info[A](val range: Text.Range, val info: A)
  {
    def restrict(r: Text.Range): Info[A] = Info(range.restrict(r), info)
    def try_restrict(r: Text.Range): Option[Info[A]] =
      try { Some(Info(range.restrict(r), info)) }
      catch { case ERROR(_) => None }
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
      else if (do_insert) i + text.length
      else (i - text.length) max start

    def convert(i: Offset): Offset = transform(is_insert, i)
    def revert(i: Offset): Offset = transform(!is_insert, i)
    def convert(range: Range): Range = range.map(convert)
    def revert(range: Range): Range = range.map(revert)


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
