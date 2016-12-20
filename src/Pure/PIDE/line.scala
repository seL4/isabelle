/*  Title:      Pure/PIDE/line.scala
    Author:     Makarius

Line-oriented text.
*/

package isabelle


import scala.annotation.tailrec


object Line
{
  /* length wrt. encoding */

  trait Length { def apply(text: String): Int }
  object Length extends Length { def apply(text: String): Int = text.length }


  /* position */

  object Position
  {
    val zero: Position = Position(0, 0)
  }

  sealed case class Position(line: Int, column: Int)
  {
    def line1: Int = line + 1
    def column1: Int = column + 1
    def print: String = line1.toString + ":" + column1.toString

    def compare(that: Position): Int =
      line compare that.line match {
        case 0 => column compare that.column
        case i => i
      }

    private def advance[A](iterator: Iterator[A], is_newline: A => Boolean): Position =
    {
      var l = line
      var c = column
      for (x <- iterator) {
        if (is_newline(x)) { l += 1; c = 0 } else c += 1
      }
      Position(l, c)
    }

    def advance(text: String): Position =
      if (text.isEmpty) this else advance[Char](text.iterator, _ == '\n')

    def advance_codepoints(text: String): Position =
      if (text.isEmpty) this else advance[Int](Codepoint.iterator(text), _ == 10)
  }


  /* range (right-open interval) */

  sealed case class Range(start: Position, stop: Position)
  {
    if (start.compare(stop) > 0)
      error("Bad line range: " + start.print + ".." + stop.print)

    def print: String = start.print + ".." + stop.print
  }


  /* document with newline as separator (not terminator) */

  object Document
  {
    val empty: Document = new Document("", Nil)

    def apply(lines: List[Line]): Document =
      if (lines.isEmpty) empty
      else new Document(lines.mkString("", "\n", ""), lines)

    def apply(text: String): Document =
      if (text.contains('\r'))
        apply(Library.cat_lines(Library.split_lines(text).map(Library.trim_line(_))))
      else if (text == "") Document.empty
      else new Document(text, Library.split_lines(text).map(Line(_)))
  }

  final class Document private(val text: String, val lines: List[Line])
  {
    override def toString: String = text

    override def equals(that: Any): Boolean =
      that match {
        case other: Document => lines == other.lines
        case _ => false
      }
    override def hashCode(): Int = lines.hashCode

    private def position(advance: (Position, String) => Position, offset: Text.Offset): Position =
    {
      @tailrec def move(i: Text.Offset, lines_count: Int, lines_rest: List[Line]): Position =
      {
        lines_rest match {
          case Nil => require(i == 0); Position(lines_count, 0)
          case line :: ls =>
            val n = line.text.length
            if (ls.isEmpty || i <= n) advance(Position(lines_count, 0), line.text.substring(n - i))
            else move(i - (n + 1), lines_count + 1, ls)
        }
      }
      move(offset, 0, lines)
    }

    def position(i: Text.Offset): Position = position(_.advance(_), i)
    def position_codepoints(i: Text.Offset): Position = position(_.advance_codepoints(_), i)

    // FIXME codepoints
    def offset(pos: Position): Option[Text.Offset] =
    {
      val l = pos.line
      val c = pos.column
      if (0 <= l && l < lines.length) {
        val line_offset =
          if (l == 0) 0
          else (0 /: lines.take(l - 1))({ case (n, line) => n + line.text.length + 1 })
        if (c <= lines(l).text.length) Some(line_offset + c) else None
      }
      else None
    }
  }


  /* line text */

  val empty: Line = new Line("")
  def apply(text: String): Line = if (text == "") empty else new Line(text)
}

final class Line private(val text: String)
{
  require(text.forall(c => c != '\r' && c != '\n'))

  lazy val length_codepoints: Int = Codepoint.iterator(text).length

  override def equals(that: Any): Boolean =
    that match {
      case other: Line => text == other.text
      case _ => false
    }
  override def hashCode(): Int = text.hashCode
  override def toString: String = text
}
