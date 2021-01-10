/*  Title:      Pure/PIDE/line.scala
    Author:     Makarius

Line-oriented text documents, with some bias towards VSCode.
*/

package isabelle


import scala.annotation.tailrec


object Line
{
  /* logical lines */

  def normalize(text: String): String =
    if (text.contains('\r')) text.replace("\r\n", "\n") else text

  def logical_lines(text: String): List[String] =
    split_lines(normalize(text))


  /* position */

  object Position
  {
    val zero: Position = Position()
    val offside: Position = Position(line = -1)

    object Ordering extends scala.math.Ordering[Position]
    {
      def compare(p1: Position, p2: Position): Int = p1 compare p2
    }
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

    def advance(text: String): Position =
      if (text.isEmpty) this
      else {
        val lines = logical_lines(text)
        val l = line + lines.length - 1
        val c = (if (l == line) column else 0) + Library.trim_line(lines.last).length
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

  object Node_Position
  {
    def offside(name: String): Node_Position = Node_Position(name, Position.offside)
  }

  sealed case class Node_Position(name: String, pos: Position = Position.zero)
  {
    def line: Int = pos.line
    def line1: Int = pos.line1
    def column: Int = pos.column
    def column1: Int = pos.column1
  }

  sealed case class Node_Range(name: String, range: Range = Range.zero)
  {
    def start: Position = range.start
    def stop: Position = range.stop
  }


  /* document with newline as separator (not terminator) */

  object Document
  {
    def apply(text: String): Document =
      Document(logical_lines(text).map(s => Line(Library.isolate_substring(s))))

    val empty: Document = apply("")

    private def split(line_text: String): List[Line] =
      if (line_text == "") List(Line.empty) else apply(line_text).lines

    private def chop(lines: List[Line]): (String, List[Line]) =
      lines match {
        case Nil => ("", Nil)
        case line :: rest => (line.text, rest)
      }

    private def length(lines: List[Line]): Int =
      if (lines.isEmpty) 0
      else ((0 /: lines) { case (n, line) => n + line.text.length + 1 }) - 1

    def text(lines: List[Line]): String = lines.mkString("", "\n", "")
  }

  sealed case class Document(lines: List[Line])
  {
    lazy val text_length: Text.Offset = Document.length(lines)
    def text_range: Text.Range = Text.Range(0, text_length)

    lazy val text: String = Document.text(lines)

    def get_text(range: Text.Range): Option[String] =
      if (text_range.contains(range)) Some(range.substring(text)) else None

    override def toString: String = text

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
          case Nil => require(i == 0, "bad Line.position.move"); Position(lines_count)
          case line :: ls =>
            val n = line.text.length
            if (ls.isEmpty || i <= n)
              Position(lines_count).advance(line.text.substring(n - i))
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
      val n = lines.length
      if (0 <= l && l < n) {
        if (0 <= c && c <= lines(l).text.length) {
          val line_offset =
            (0 /: lines.iterator.take(l)) { case (n, line) => n + line.text.length + 1 }
          Some(line_offset + c)
        }
        else None
      }
      else if (l == n && c == 0) Some(text_length)
      else None
    }

    def change(remove: Range, insert: String): Option[(List[Text.Edit], Document)] =
    {
      for {
        edit_start <- offset(remove.start)
        if remove.stop == remove.start || offset(remove.stop).isDefined
        l1 = remove.start.line
        l2 = remove.stop.line
        if l1 <= l2
        (removed_text, new_lines) <-
        {
          val c1 = remove.start.column
          val c2 = remove.stop.column

          val (prefix, lines1) = lines.splitAt(l1)
          val (s1, rest1) = Document.chop(lines1)

          if (l1 == l2) {
            if (0 <= c1 && c1 <= c2 && c2 <= s1.length) {
              Some(
                if (lines1.isEmpty) ("", prefix ::: Document.split(insert))
                else {
                  val removed_text = s1.substring(c1, c2)
                  val changed_text = s1.substring(0, c1) + insert + s1.substring(c2)
                  (removed_text, prefix ::: Document.split(changed_text) ::: rest1)
                })
            }
            else None
          }
          else {
            val (middle, lines2) = rest1.splitAt(l2 - l1 - 1)
            val (s2, rest2) = Document.chop(lines2)
            if (0 <= c1 && c1 <= s1.length && 0 <= c2 && c2 <= s2.length) {
              Some(
                if (lines1.isEmpty) ("", prefix ::: Document.split(insert))
                else {
                  val r1 = s1.substring(c1)
                  val r2 = s2.substring(0, c2)
                  val removed_text =
                    if (lines2.isEmpty) Document.text(Line(r1) :: middle)
                    else Document.text(Line(r1) :: middle ::: List(Line(r2)))
                  val changed_text = s1.substring(0, c1) + insert + s2.substring(c2)
                  (removed_text, prefix ::: Document.split(changed_text) ::: rest2)
                })
            }
            else None
          }
        }
      }
      yield
        (Text.Edit.removes(edit_start, removed_text) ::: Text.Edit.inserts(edit_start, insert),
          Document(new_lines))
    }
  }


  /* line text */

  val empty: Line = new Line("")
  def apply(text: String): Line = if (text == "") empty else new Line(text)
}

final class Line private(val text: String)
{
  require(text.forall(c => c != '\r' && c != '\n'), "bad line text")

  override def equals(that: Any): Boolean =
    that match {
      case other: Line => text == other.text
      case _ => false
    }
  override def hashCode(): Int = text.hashCode
  override def toString: String = text
}
