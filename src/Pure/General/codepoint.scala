/*  Title:      Pure/General/codepoint.scala
    Author:     Makarius

Unicode codepoints vs. Unicode string encoding.
*/

package isabelle


object Codepoint
{
  def string(c: Int): String = new String(Array(c), 0, 1)

  def iterator(s: String): Iterator[Int] =
    new Iterator[Int] {
      var offset = 0
      def hasNext: Boolean = offset < s.length
      def next: Int =
      {
        val c = s.codePointAt(offset)
        offset += Character.charCount(c)
        c
      }
    }

  def length(s: String): Int = iterator(s).length
  object Length extends Line.Length { def apply(s: String): Int = Codepoint.length(s) }
}
