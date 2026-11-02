/*  Title:      Pure/General/position.scala
    Author:     Makarius

Position properties.
*/

package isabelle


import scala.annotation.tailrec
import scala.util.parsing.{input, combinator}


object Position {
  type T = Properties.T

  val none: T = Nil

  val Line = new Properties.Int(Markup.LINE)
  val Offset = new Properties.Int(Markup.OFFSET)
  val End_Offset = new Properties.Int(Markup.END_OFFSET)
  val Label = new Properties.String(Markup.LABEL)
  val File = new Properties.String(Markup.FILE)
  val Id = new Properties.Long(Markup.ID)
  val Id_String = new Properties.String(Markup.ID)

  val Def_Line = new Properties.Int(Markup.DEF_LINE)
  val Def_Offset = new Properties.Int(Markup.DEF_OFFSET)
  val Def_End_Offset = new Properties.Int(Markup.DEF_END_OFFSET)
  val Def_Label = new Properties.String(Markup.DEF_LABEL)
  val Def_File = new Properties.String(Markup.DEF_FILE)
  val Def_Id = new Properties.Long(Markup.DEF_ID)

  object Line_File {
    def apply(line: Int, file: String): T =
      (if (line > 0) Line(line) else Nil) :::
      (if (file.nonEmpty) File(file) else Nil)

    def unapply(pos: T): Option[(Int, String)] =
      (pos, pos) match {
        case (Line(i), File(name)) => Some((i, name))
        case (_, File(name)) => Some((1, name))
        case _ => None
      }
  }

  object Def_Line_File {
    def unapply(pos: T): Option[(Int, String)] =
      (pos, pos) match {
        case (Def_Line(i), Def_File(name)) => Some((i, name))
        case (_, Def_File(name)) => Some((1, name))
        case _ => None
      }
  }

  object Range {
    def apply(range: Symbol.Range): T = Offset(range.start) ::: End_Offset(range.stop)
    def unapply(pos: T): Option[Symbol.Range] =
      (pos, pos) match {
        case (Offset(start), End_Offset(stop)) if start <= stop => Some(Text.Range(start, stop))
        case (Offset(start), _) => Some(Text.Range(start, start + 1))
        case _ => None
      }
  }

  object Def_Range {
    def apply(range: Symbol.Range): T = Def_Offset(range.start) ::: Def_End_Offset(range.stop)
    def unapply(pos: T): Option[Symbol.Range] =
      (pos, pos) match {
        case (Def_Offset(start), Def_End_Offset(stop)) if start <= stop => Some(Text.Range(start, stop))
        case (Def_Offset(start), _) => Some(Text.Range(start, start + 1))
        case _ => None
      }
  }

  object Item_Id {
    def unapply(pos: T): Option[(Long, Symbol.Range)] =
      pos match {
        case Id(id) =>
          val offset = Offset.unapply(pos) getOrElse 0
          val end_offset = End_Offset.unapply(pos) getOrElse (offset + 1)
          Some((id, Text.Range(offset, end_offset)))
        case _ => None
      }
  }

  object Item_Def_Id {
    def unapply(pos: T): Option[(Long, Symbol.Range)] =
      pos match {
        case Def_Id(id) =>
          val offset = Def_Offset.unapply(pos) getOrElse 0
          val end_offset = Def_End_Offset.unapply(pos) getOrElse (offset + 1)
          Some((id, Text.Range(offset, end_offset)))
        case _ => None
      }
  }

  object Item_File {
    def unapply(pos: T): Option[(String, Int, Symbol.Range)] =
      pos match {
        case Line_File(line, name) =>
          val offset = Offset.unapply(pos) getOrElse 0
          val end_offset = End_Offset.unapply(pos) getOrElse (offset + 1)
          Some((name, line, Text.Range(offset, end_offset)))
        case _ => None
      }
  }

  object Item_Def_File {
    def unapply(pos: T): Option[(String, Int, Symbol.Range)] =
      pos match {
        case Def_Line_File(line, name) =>
          val offset = Def_Offset.unapply(pos) getOrElse 0
          val end_offset = Def_End_Offset.unapply(pos) getOrElse (offset + 1)
          Some((name, line, Text.Range(offset, end_offset)))
        case _ => None
      }
  }


  /* here: user output */

  def here(props: T, delimited: Boolean = true): String = {
    val pos = props.filter(Markup.position_property)
    if_proper(pos,
      {
        val s0 =
          (Line.unapply(pos), File.unapply(pos)) match {
            case (Some(i), None) => "line " + i.toString
            case (Some(i), Some(name)) => "line " + i.toString + " of " + quote(name)
            case (None, Some(name)) => "file " + quote(name)
            case _ => ""
          }
        val s = if (s0 == "") s0 else if (delimited) " (" + s0 + ")" else s0
        Markup(Markup.POSITION, pos).markup(s)
      })
  }


  /* JSON representation */

  object JSON {
    def apply(pos: T): isabelle.JSON.Object.T =
      isabelle.JSON.Object.empty ++
        Line.unapply(pos).map(Line.name -> _) ++
        Offset.unapply(pos).map(Offset.name -> _) ++
        End_Offset.unapply(pos).map(End_Offset.name -> _) ++
        File.unapply(pos).map(File.name -> _) ++
        Id.unapply(pos).map(Id.name -> _)

    def unapply(json: isabelle.JSON.T): Option[T] =
      for {
        line <- isabelle.JSON.int_default(json, Line.name)
        offset <- isabelle.JSON.int_default(json, Offset.name)
        end_offset <- isabelle.JSON.int_default(json, End_Offset.name)
        file <- isabelle.JSON.string_default(json, File.name)
        id <- isabelle.JSON.long_default(json, Id.name)
      }
      yield {
        def defined(name: String): Boolean = isabelle.JSON.value(json, name).isDefined
        (if (defined(Line.name)) Line(line) else Nil) :::
        (if (defined(Offset.name)) Offset(offset) else Nil) :::
        (if (defined(End_Offset.name)) End_Offset(end_offset) else Nil) :::
        (if (defined(File.name)) File(file) else Nil) :::
        (if (defined(Id.name)) Id(id) else Nil)
      }
  }


  /* reader with position */

  trait S {
    def source: String
    def content: String
  }

  object P {
    val none: P = new P(0, 0, "", "")
    val start: P = new P(1, 1, "", "")
    def file(file: String): P = new P(1, 1, file, "")
    def id(id: String): P = new P(0, 1, "", id)
    val command: P = id(Markup.COMMAND)
  }

  final class P private[Position](
      val line: Int,
      val offset: Symbol.Offset,
      val file: String,
      val id: String)
  extends input.Position {
    def column = 0
    def lineContents = ""

    def advance(s: S): P = advance(s.source)
    def advance(source: String): P = {
      var line1 = line
      var offset1 = offset
      for (s <- Symbol.iterator(source)) {
        if (line1 > 0 && Symbol.is_newline(s)) line1 += 1
        if (offset1 > 0) offset1 += 1
      }
      if (line1 == line && offset1 == offset) this
      else new P(line1, offset1, file, id)
    }

    def position(end_offset: Symbol.Offset): T =
      (if (line > 0) Line(line) else Nil) :::
      (if (offset > 0) Offset(offset) else Nil) :::
      (if (end_offset > 0) End_Offset(end_offset) else Nil) :::
      (if (file.nonEmpty) File(file) else Nil) :::
      (if (id.nonEmpty) Id_String(id) else Nil)

    def position(): T = position(0)
    def position(s: S): T = position(advance(s).offset)
    def position(source: String): T = position(advance(source).offset)

    override def toString: String = here(position(), delimited = false)
  }

  class Reader[Elem <: S] private[Position](inp: List[Elem], val pos: P)
  extends input.Reader[Elem] {
    def first: Elem = inp.head
    def rest: Reader[Elem] = new Reader[Elem](inp.tail, pos.advance(first))
    def atEnd: Boolean = inp.isEmpty
  }

  def reader[Elem <: S](inp: List[Elem], start: P): Reader[Elem] =
    new Reader[Elem](inp, start)


  /* combinator parsers */

  trait E extends S {
    def kind: Any
    def is_proper: Boolean
  }

  trait Parsers extends combinator.Parsers {
    type Elem <: E

    def filter_proper: Boolean = true

    @tailrec private def proper(in: Input): Input =
      if (!filter_proper || in.atEnd || in.first.is_proper) in
      else proper(in.rest)

    private def proper_position: Parser[T] = { (raw_input: Input) =>
      val in = proper(raw_input)
      val pos =
        in.pos match {
          case pos: P => pos
          case _ => P.none
        }
      Success(if (in.atEnd) pos.position() else pos.position(in.first.source), in)
    }

    def position[A](parser: Parser[A]): Parser[(A, T)] =
      proper_position ~ parser ^^ { case x ~ y => (y, x) }

    def element(what: String, pred: Elem => Boolean): Parser[Elem] = { (raw_input: Input) =>
      val in = proper(raw_input)
      if (in.atEnd) Failure(what + " expected,\nbut end-of-input was found", in)
      else {
        val elem = in.first
        if (pred(elem)) Success(elem, proper(in.rest))
        else Failure(what + " expected,\nbut " + elem.kind + " was found:\n" + elem.source, in)
      }
    }

    def atom(what: String, pred: Elem => Boolean): Parser[String] =
      element(what, pred) ^^ (_.content)


    /* wrappers */

    def parse[T](p: Parser[T], in: Reader[Elem]): ParseResult[T] = p(in)

    def parse_all[T](p: Parser[T], in: Reader[Elem]): ParseResult[T] = {
      val result = parse(p, in)
      val rest = proper(result.next)
      if (result.successful && !rest.atEnd) Error("bad input", rest)
      else result
    }
  }
}
