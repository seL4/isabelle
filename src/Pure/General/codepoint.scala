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

  trait Length extends isabelle.Length
  {
    protected def codepoint_length(c: Int): Int = 1

    def apply(s: String): Int =
      (0 /: iterator(s)) { case (n, c) => n + codepoint_length(c) }

    def offset(s: String, i: Int): Option[Text.Offset] =
    {
      if (i <= 0 || s.forall(_ < 0x80)) isabelle.Length.offset(s, i)
      else {
        val length = s.length
        var offset = 0
        var j = 0
        while (offset < length && j < i) {
          val c = s.codePointAt(offset)
          offset += Character.charCount(c)
          j += codepoint_length(c)
        }
        if (j >= i) Some(offset) else None
      }
    }
  }

  object Length extends Length
}
