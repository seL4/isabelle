/*  Title:      Pure/PIDE/line.scala
    Author:     Makarius

Line-oriented text.
*/

package isabelle


import scala.annotation.tailrec


object Line
{
  /* position */

  object Position
  {
    val zero: Position = Position()
  }

  sealed case class Position(line: Int = 0, column: Int = 0)
  {
    def line1: Int = line + 1
    def column1: Int = column + 1
    def print: String = line1.toString + ":" + column1.toString

    def compare(that: Position): Int =
      line compare that.line match {
        case 0 => column compare that.column
        case i => i
      }

    def advance(text: String, length: Length = Length): Position =
      if (text.isEmpty) this
      else {
        val lines = Library.split_lines(text)
        val l = line + lines.length - 1
        val c = (if (l == line) column else 0) + length(Library.trim_line(lines.last))
        Position(l, c)
      }
  }


  /* range (right-open interval) */

  object Range
  {
    val zero: Range = Range(Position.zero, Position.zero)
  }

  sealed case class Range(start: Position, stop: Position)
  {
    if (start.compare(stop) > 0)
      error("Bad line range: " + start.print + ".." + stop.print)

    def print: String =
      if (start == stop) start.print
      else start.print + ".." + stop.print
  }


  /* positions within document node */

  sealed case class Position_Node(pos: Position, name: String)
  {
    def line: Int = pos.line
    def column: Int = pos.column
  }

  sealed case class Range_Node(range: Range, name: String)
  {
    def start: Position = range.start
    def stop: Position = range.stop
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

    def position(offset: Text.Offset, length: Length = Length): Position =
    {
      @tailrec def move(i: Text.Offset, lines_count: Int, lines_rest: List[Line]): Position =
      {
        lines_rest match {
          case Nil => require(i == 0); Position(lines_count)
          case line :: ls =>
            val n = line.text.length
            if (ls.isEmpty || i <= n)
              Position(lines_count).advance(line.text.substring(n - i), length)
            else move(i - (n + 1), lines_count + 1, ls)
        }
      }
      move(offset, 0, lines)
    }

    def offset(pos: Position, length: Length = Length): Option[Text.Offset] =
    {
      val l = pos.line
      val c = pos.column
      if (0 <= l && l < lines.length) {
        val line_offset =
          if (l == 0) 0
          else (0 /: lines.iterator.take(l - 1))({ case (n, line) => n + length(line.text) + 1 })
        length.offset(lines(l).text, c).map(line_offset + _)
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
