/*  Title:      Pure/General/codepoint.scala
    Author:     Makarius

Unicode codepoints vs. Unicode string encoding.
*/

package isabelle

import isabelle.Text.Offset


object Codepoint
{
  def string(c: Int): String = new String(Array(c), 0, 1)

  private class Iterator_Offset[A](s: String, result: (Int, Text.Offset) => A)
    extends Iterator[A]
  {
    var offset = 0
    def hasNext: Boolean = offset < s.length
    def next(): A =
    {
      val c = s.codePointAt(offset)
      val i = offset
      offset += Character.charCount(c)
      result(c, i)
    }
  }

  def iterator_offset(s: String): Iterator[(Int, Text.Offset)] = new Iterator_Offset(s, (_, _))
  def iterator(s: String): Iterator[Int] = new Iterator_Offset(s, (c, _) => c)

  def length(s: String): Int = iterator(s).length
}
