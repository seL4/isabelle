/*  Title:      Pure/General/codepoint.scala
    Author:     Makarius

Unicode codepoints vs. Unicode string encoding.
*/

package isabelle


object Codepoint
{
  def iterator(str: String): Iterator[Int] =
    new Iterator[Int] {
      var offset = 0
      def hasNext: Boolean = offset < str.length
      def next: Int =
      {
        val c = str.codePointAt(offset)
        offset += Character.charCount(c)
        c
      }
    }

  def string(c: Int): String = new String(Array(c), 0, 1)
}
