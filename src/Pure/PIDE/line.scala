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

    def advance(text: String, text_length: Text.Length): Position =
      if (text.isEmpty) this
      else {
        val lines = Library.split_lines(text)
        val l = line + lines.length - 1
        val c = (if (l == line) column else 0) + text_length(Library.trim_line(lines.last))
        Position(l, c)
      }
  }


  /* range (right-open interval) */

  object Range
  {
    def apply(start: Position): Range = Range(start, start)
    val zero: Range = Range(Position.zero)
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

  sealed case class Node_Position(name: String, pos: Position = Position.zero)
  {
    def line: Int = pos.line
    def column: Int = pos.column
  }

  sealed case class Node_Range(name: String, range: Range = Range.zero)
  {
    def start: Position = range.start
    def stop: Position = range.stop
  }


  /* document with newline as separator (not terminator) */

  object Document
  {
    def apply(text: String, text_length: Text.Length): Document =
      if (text.contains('\r'))
        Document(Library.split_lines(text).map(s => Line(Library.trim_line(s))), text_length)
      else
        Document(Library.split_lines(text).map(s => Line(s)), text_length)
  }

  sealed case class Document(lines: List[Line], text_length: Text.Length)
  {
    def make_text: String = lines.mkString("", "\n", "")

    override def toString: String = make_text

    override def equals(that: Any): Boolean =
      that match {
        case other: Document => lines == other.lines
        case _ => false
      }
    override def hashCode(): Int = lines.hashCode

    def position(text_offset: Text.Offset): Position =
    {
      @tailrec def move(i: Text.Offset, lines_count: Int, lines_rest: List[Line]): Position =
      {
        lines_rest match {
          case Nil => require(i == 0); Position(lines_count)
          case line :: ls =>
            val n = line.text.length
            if (ls.isEmpty || i <= n)
              Position(lines_count).advance(line.text.substring(n - i), text_length)
            else move(i - (n + 1), lines_count + 1, ls)
        }
      }
      move(text_offset, 0, lines)
    }

    def range(text_range: Text.Range): Range =
      Range(position(text_range.start), position(text_range.stop))

    def offset(pos: Position): Option[Text.Offset] =
    {
      val l = pos.line
      val c = pos.column
      if (0 <= l && l < lines.length) {
        val line_offset =
          if (l == 0) 0
          else (0 /: lines.iterator.take(l - 1)) { case (n, line) => n + text_length(line.text) + 1 }
        text_length.offset(lines(l).text, c).map(line_offset + _)
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
