/*  Title:      Pure/General/toml.scala
    Author:     Fabian Huch, TU Muenchen

Support for TOML: https://toml.io/en/v1.0.0
*/

package isabelle


import TOML.Parse_Context.Seen

import java.lang.Long.parseLong
import java.lang.{String => Str}
import java.time.{LocalDate, LocalDateTime, LocalTime, OffsetDateTime}

import scala.{Boolean => Bool}
import scala.collection.immutable.ListMap
import scala.reflect.{ClassTag, classTag}
import scala.util.Try
import scala.util.matching.Regex
import scala.util.parsing.combinator
import scala.util.parsing.combinator.lexical.Scanners
import scala.util.parsing.input
import scala.util.parsing.input.Positional
import scala.util.parsing.input.CharArrayReader.EofCh


object TOML {
  /* typed representation and access */

  type Key = Str

  sealed trait T
  case class String(rep: Str) extends T
  case class Integer(rep: Long) extends T
  case class Float(rep: Double) extends T
  case class Boolean(rep: Bool) extends T
  case class Offset_Date_Time(rep: OffsetDateTime) extends T
  case class Local_Date_Time(rep: LocalDateTime) extends T
  case class Local_Date(rep: LocalDate) extends T
  case class Local_Time(rep: LocalTime) extends T

  object Scalar {
    def unapply(t: T): Option[Str] =
      t match {
        case s: String => Some(s.rep)
        case i: Integer => Some(i.rep.toString)
        case f: Float => Some(f.rep.toString)
        case b: Boolean => Some(b.rep.toString)
        case o: Offset_Date_Time => Some(o.rep.toString)
        case l: Local_Date_Time => Some(l.rep.toString)
        case l: Local_Date => Some(l.rep.toString)
        case l: Local_Time => Some(l.rep.toString)
        case _ => None
      }
  }

  class Array private(private val rep: List[T]) extends T {
    override def hashCode(): Int = rep.hashCode()
    override def equals(that: Any): Bool = that match {
      case other: Array => rep == other.rep
      case _ => false
    }
    override def toString: Str = "Array(" + length.toString + ")"

    class Values[A](pf: PartialFunction[T, A]) { def values: List[A] = rep.collect(pf).reverse }
    lazy val string = new Values({ case s: String => s })
    lazy val integer = new Values({ case i: Integer => i })
    lazy val float = new Values({ case f: Float => f })
    lazy val boolean = new Values({ case b: Boolean => b })
    lazy val offset_date_time = new Values({ case o: Offset_Date_Time => o })
    lazy val local_date_time = new Values({ case l: Local_Date_Time => l })
    lazy val local_date = new Values({ case l: Local_Date => l })
    lazy val local_time = new Values({ case l: Local_Time => l })
    lazy val array = new Values({ case a: Array => a })
    lazy val table = new Values({ case t: Table => t })
    lazy val any = new Values({ case t => t })

    def +(elem: T): Array = new Array(elem :: rep)
    def ++(other: Array): Array = new Array(other.rep ::: rep)
    def length: Int = rep.length
    def is_empty: Bool = rep.isEmpty
  }

  object Array {
    def apply(elems: Iterable[T]): Array = new Array(elems.toList.reverse)
    def apply(elems: T*): Array = Array(elems)
    val empty: Array = apply()
  }

  class Table private(private val rep: ListMap[Key, T]) extends T {
    override def hashCode(): Int = rep.hashCode()
    override def equals(that: Any): Bool =
      that match {
        case other: Table => rep == other.rep
        case _ => false
      }
    override def toString: Str =
      rep.map {
        case (k, t: Table) => k + "(" + t.domain.size + ")"
        case (k, a: Array) => k + "(" + a.length + ")"
        case (k, _) => k
      }.mkString("Table(", ", ", ")")

    class Value[A: ClassTag](pf: PartialFunction[T, A]) {
      def values: List[(Key, A)] =
        rep.toList.collect { case (k, v) if pf.isDefinedAt(v) => k -> pf(v) }
      def get(k: Key): Option[A] = rep.get(k).flatMap(v => PartialFunction.condOpt(v)(pf))
      def apply(k: Key): A =
        rep.get(k) match {
          case Some(v) => PartialFunction.condOpt(v)(pf) match {
            case Some(value) => value
            case None =>
              error("Expected" + classTag[A].runtimeClass.getName +
                ", got " + v.getClass.getSimpleName + " for key " + quote(k))
          }
          case None => error("Key " + quote(k) + " does not exist")
        }
    }

    lazy val string = new Value({ case s: String => s })
    lazy val integer = new Value({ case i: Integer => i })
    lazy val float = new Value({ case f: Float => f })
    lazy val boolean = new Value({ case b: Boolean => b })
    lazy val offset_date_time = new Value({ case o: Offset_Date_Time => o })
    lazy val local_date_time = new Value({ case l: Local_Date_Time => l })
    lazy val local_date = new Value({ case l: Local_Date => l })
    lazy val local_time = new Value({ case l: Local_Time => l })
    lazy val array = new Value({ case a: Array => a })
    lazy val table = new Value({ case t: Table => t })
    lazy val any = new Value({ case t => t })

    def +(elem: (Key, T)): Table = {
      val (k, v) = elem
      val v1 = rep.get(k) match {
        case None => v
        case Some(v0) =>
          (v0, v) match {
            case (t0: Table, t: Table) => t0 ++ t
            case (a0: Array, a: Array) => a0 ++ a
            case _ => v
          }
      }
      new Table(rep + (k -> v1))
    }
    def -(k: Key): Table = new Table(rep - k)
    def ++(other: Table): Table =  other.rep.foldLeft(this)(_ + _)
    def domain: Set[Key] = rep.keySet
    def is_empty: Bool = rep.isEmpty
  }

  object Table {
    def apply(elems: Iterable[(Key, T)]): Table = elems.foldLeft(new Table(ListMap.empty))(_ + _)
    def apply(elems: (Key, T)*): Table = Table(elems)
    val empty: Table = apply()
  }


  /* lexer */

  enum Kind { case KEYWORD, VALUE, STRING, MULTILINE_STRING, LINE_SEP, ERROR }

  sealed case class Token(kind: Kind, text: Str) extends Positional {
    def is_keyword(name: Str): Bool = kind == Kind.KEYWORD && text == name
    def is_value: Bool = kind == Kind.VALUE
    def is_string: Bool = kind == Kind.STRING
    def is_multiline_string: Bool = kind == Kind.MULTILINE_STRING
    def is_line_sep: Bool = kind == Kind.LINE_SEP
  }

  object Lexer extends Scanners with Scan.Parsers {
    override type Elem = Char
    type Token = TOML.Token

    def errorToken(msg: Str): Token = Token(Kind.ERROR, msg)

    val white_space: Str = " \t"
    override val whiteSpace: Regex = ("[" + white_space + "]+").r
    override def whitespace: Parser[Any] = rep(comment | many1(character(white_space.contains(_))))

    def line_sep: Parser[Str] = rep1("\n" | s"\r\n" | EofCh) ^^ (cs => cs.mkString)
    def line_sep_token: Parser[Token] = line_sep ^^ (s => Token(Kind.LINE_SEP, s))

    def is_control(e: Elem): Bool =
      e <= '\u0008' || ('\u000A' <= e && e <= '\u001F') || e == '\u007F'

    override def comment: Parser[Str] = '#' ~>! many(character(c => !is_control(c)))

    def keyword: Parser[Token] = one(character("{}[],=.".contains)) ^^ (s => Token(Kind.KEYWORD, s))

    def is_value(c: Elem): Bool =
      Symbol.is_ascii_letter(c) || Symbol.is_ascii_digit(c) || "_-:+".contains(c)
    def value: Parser[Token] =
      many1(character(is_value)) ~
        opt(' ' ~ many1(character(is_value)) ^^ { case ws ~ s => ws.toString + s }) ~
        opt('.' ~ many1(character(is_value)) ^^ { case dot ~ s => dot.toString + s}) ^^
        { case s ~ ss ~ sd => Token(Kind.VALUE, s + ss.getOrElse("") + sd.getOrElse("")) }

    def string: Parser[Token] =
      multiline_basic_string | basic_string | multiline_literal_string | literal_string

    private def trim(s: Str): Str =
      if (s.startsWith("\n")) s.stripPrefix("\n") else s.stripPrefix("\r\n")

    def basic_string: Parser[Token] =
      '"' ~> rep(basic_string_elem) <~ '"' ^^ (cs => Token(Kind.STRING, cs.mkString))

    def multiline_basic_string: Parser[Token] =
      "\"\"\"" ~>
        rep(multiline_basic_string_elem |
          ("\"\"" | "\"") ~ multiline_basic_string_elem ^^ { case s ~ t => s + t }) ~
        repeated(character(_ == '"'), 3, 5) ^^ { case cs ~ q =>
          Token(Kind.MULTILINE_STRING, trim(cs.mkString + q.drop(3))) }

    private def multiline_basic_string_elem: Parser[Str] =
      ('\\' ~ line_sep ~ rep(many1(character(white_space.contains)) | line_sep)) ^^ (_ => "") |
        basic_string_elem ^^ (_.toString) | line_sep

    def literal_string: Parser[Token] =
      '\'' ~> rep(literal_string_elem) <~ '\'' ^^ (cs => Token(Kind.STRING, cs.mkString))

    def multiline_literal_string: Parser[Token] =
      "'''" ~>
        rep(multiline_literal_string_elem |
          ("''" | "'") ~ multiline_literal_string_elem ^^ { case s ~ t => s + t }) ~
        repeated(character(_ == '\''), 3, 5) ^^ { case cs ~ q =>
          Token(Kind.MULTILINE_STRING, trim(cs.mkString + q.drop(3))) }

    private def multiline_literal_string_elem: Parser[Str] =
      line_sep | literal_string_elem ^^ (_.toString)

    private def basic_string_elem: Parser[Elem] =
      elem("", c => !is_control(c) && !"\"\\".contains(c)) | '\\' ~> string_escape

    private def string_escape: Parser[Elem] =
      elem("", "\"\\".contains(_)) |
        elem("", "btnfr".contains(_)) ^^
          { case 'b' => '\b' case 't' => '\t' case 'n' => '\n' case 'f' => '\f' case 'r' => '\r' } |
        ('u' ~> repeated(character(Symbol.is_ascii_hex), 4, 4) |
          'U' ~> repeated(character(Symbol.is_ascii_hex), 8, 8)) ^^
          (s => java.lang.Integer.parseInt(s, 16).toChar)

    private def literal_string_elem: Parser[Elem] = elem("", c => !is_control(c) && c != '\'')

    def string_failure: Parser[Token] = ("\"" | "'") ~> failure("Unterminated string")

    def token: Parser[Token] =
      positioned(
        line_sep_token | keyword | value | string | string_failure | failure("Unrecognized token"))
  }


  /* parser */

  trait Parsers extends combinator.Parsers {
    type Elem = Token


    /* parse structure */

    sealed trait V extends Positional
    case class Primitive(t: T) extends V
    case class Array(rep: List[V]) extends V
    case class Inline_Table(elems: List[(Keys, V)]) extends V

    sealed trait Def extends Positional
    case class Table(key: Keys, elems: List[(Keys, V)]) extends Def
    case class Array_Of_Tables(key: Keys, elems: List[(Keys, V)]) extends Def

    case class File(elems: List[(Keys, V)], defs: List[Def])


    /* top-level syntax structure */

    def key: Parser[Keys] = positioned(rep1sep(keys, $$$(".")) ^^ (_.reduce(_ ++ _)))

    def string: Parser[String] =
      elem("string", e => e.is_string || e.is_multiline_string) ^^ (s => String(s.text))
    def integer: Parser[Integer] =
      (decimal_int | binary_int | octal_int | hexadecimal_int) ^^ Integer.apply
    def float: Parser[Float] = (symbol_float | number_float) ^^ Float.apply
    def boolean: Parser[Boolean] = token("boolean", _.is_value, s => Boolean(Value.Boolean.parse(s)))

    def offset_date_time: Parser[Offset_Date_Time] =
      token("offset date-time", _.is_value,
        s => Offset_Date_Time(OffsetDateTime.parse(s.replace(" ", "T"))))
    def local_date_time: Parser[Local_Date_Time] =
      token("local date-time", _.is_value,
        s => Local_Date_Time(LocalDateTime.parse(s.replace(" ", "T"))))
    def local_date: Parser[Local_Date] =
      token("local date", _.is_value, s => Local_Date(LocalDate.parse(s)))
    def local_time: Parser[Local_Time] =
      token("local time", _.is_value, s => Local_Time(LocalTime.parse(s)))

    def array: Parser[Array] =
      positioned(
        $$$("[") ~>! repsep(opt(line_sep) ~> toml_value, opt(line_sep) ~ $$$(",")) <~!
          opt(line_sep) ~! opt($$$(",")) ~! opt(line_sep) <~! $$$("]") ^^ Array.apply)

    def inline_table: Parser[Inline_Table] =
      positioned(
        $$$("{") ~>! repsep(pair, $$$(",")) <~! $$$("}") ^^ Inline_Table.apply)

    def pair: Parser[(Keys, V)] = (key <~! $$$("=")) ~! toml_value ^^ { case ks ~ v => (ks, v) }

    def table: Parser[Table] =
      positioned(
        $$$("[") ~> (key <~! $$$("]") ~! line_sep) ~! content ^^
          { case key ~ content => Table(key, content) })

    def array_of_tables: Parser[Array_Of_Tables] =
      positioned(
        $$$("[") ~ $$$("[") ~>! (key <~! $$$("]") ~! $$$("]") ~! line_sep) ~! content ^^
          { case key ~ content => Array_Of_Tables(key, content) })

    def toml: Parser[File] =
      (opt(line_sep) ~>! content ~! rep(table | array_of_tables)) ^^
        { case content ~ defs => File(content, defs) }


    /* auxiliary */

    private def $$$(name: Str): Parser[Token] = elem(name, _.is_keyword(name))
    private def maybe[A, B](p: Parser[A], f: A => B): Parser[B] =
      p ^^ (a => Try(f(a))) ^? { case util.Success(v) => v }
    private def token[A](name: Str, p: Token => Bool, parser: Str => A): Parser[A] =
      maybe(elem(name, p), s => parser(s.text))
    private def prefixed[A](
      prefix: Str, name: Str, p: Str => Bool, parser: Str => A
    ): Parser[A] =
      token(name, e => e.is_value && e.text.startsWith(prefix) && p(e.text.stripPrefix(prefix)),
        s => parser(s.stripPrefix(prefix)))

    private def is_key(e: Elem): Bool = e.is_value && !e.text.exists("+: ".contains(_))
    private def keys: Parser[Keys] =
      token("string key", _.is_string, Keys.quoted) | token("key", is_key, Keys.dotted)

    private def sep_surrounded(s: Str): Bool =
      !s.startsWith("_") && !s.endsWith("_") && s.split('_').forall(_.nonEmpty)
    private def no_leading_zero(s: Str): Bool = {
      val t = s.replaceAll("_", "").takeWhile(_.isDigit)
      t == "0" || !t.startsWith("0")
    }

    private def is_int(s: Str): Bool =
      no_leading_zero(s.replaceAll("[-+]", "")) && sep_surrounded(s.replaceAll("[-+]", ""))
    private def decimal_int: Parser[Long] =
      token("integer", e => e.is_value && is_int(e.text), _.replace("_", "").toLong)
    private def binary_int: Parser[Long] =
      prefixed("0b", "integer", sep_surrounded, s => parseLong(s.replace("_", ""), 2))
    private def octal_int: Parser[Long] =
      prefixed("0o", "integer", sep_surrounded, s => parseLong(s.replace("_", ""), 8))
    private def hexadecimal_int: Parser[Long] =
      prefixed("0x", "integer", sep_surrounded, s => parseLong(s.replace("_", ""), 16))

    private def is_float(s: Str): Bool =
      s.exists(".eE".contains) && s.count("eE".contains) <= 1 &&
        no_leading_zero(s.replaceAll("[-+]", "")) &&
        sep_surrounded(s.replaceAll("[-+]", "").replaceAll("[.eE][+\\-]?", "_"))
    private def number_float: Parser[Double] =
      token("float", e => e.is_value && is_float(e.text), _.replace("_", "").toDouble)
    private def symbol_float: Parser[Double] =
      token("float", _.is_value, {
        case "inf" | "+inf" => Double.PositiveInfinity
        case "-inf" => Double.NegativeInfinity
        case "nan" | "+nan" | "-nan" => Double.NaN
      })

    private def toml_value: Parser[V] =
      positioned(
        (string | float | integer | boolean | offset_date_time |
          local_date_time | local_date | local_time) ^^ Primitive.apply | array | inline_table)

    private def line_sep: Parser[Any] = rep1(elem("line sep", _.is_line_sep))

    private def content: Parser[List[(Keys, V)]] =
      rep((key <~! $$$("=")) ~! toml_value <~! line_sep ^^ { case ks ~ v => ks -> v })
  }

  object Parsers extends Parsers


  /* Keys for nested tables */

  object Keys {
    def empty: Keys = new Keys(Nil)
    def quoted(s: Str): Keys = new Keys(List(s))
    def dotted(s: Str): Keys = new Keys(s.split('.').toList)
  }

  class Keys private(private val rep: List[Key]) extends Positional {
    override def hashCode(): Int = rep.hashCode()
    override def equals(obj: Any): Bool =
      obj match {
        case other: Keys => rep == other.rep
        case _ => false
      }
    override def toString: Str = rep.mkString("Keys(", ".", ")")

    def first: Keys = new Keys(rep.take(1))
    def last: Keys = new Keys(rep.takeRight(1))
    def next: Keys = new Keys(rep.drop(1))
    def parent: Keys = new Keys(rep.dropRight(1))

    def the_key: Key = Library.the_single(rep)

    def length: Int = rep.length

    def ++(other: Keys): Keys = new Keys(rep ::: other.rep)

    def prefixes: Set[Keys] = splits.map(_._1).toSet
    def splits: List[(Keys, Keys)] = Range.inclusive(0, length).toList.map(split).reverse
    def split(i: Int): (Keys, Keys) = {
      val (rep0, rep1) = rep.splitAt(i)
      (new Keys(rep0), new Keys(rep1))
    }

    def is_child_of(parent: Keys): Bool = rep.startsWith(parent.rep)
  }


  /* checking and translating parse structure into toml */

  class Parse_Context private(var seen_tables: Map[Keys, Seen], file: Option[Path] = None) {
    private def recent_array(ks: Keys): (Keys, Seen, Keys) =
      ks.splits.collectFirst {
        case (ks1, ks2) if seen_tables.contains(ks1) => (ks1, seen_tables(ks1), ks2)
      }.get

    private def check_add(start: Int, ks: Keys, elem: Parsers.Def | Parsers.V): Unit = {
      val (to, seen, rest, split) =
        elem match {
          case _: Parsers.Array_Of_Tables =>
            val (_, seen, rest) = recent_array(ks.parent)
            (ks, seen, rest ++ ks.last, 0)
          case _ =>
            val (to, seen, rest) = recent_array(ks)
            (to, seen, rest, start - to.length)
        }
      val (rest0, rest1) = rest.split(split)
      val implicitly_seen = rest1.parent.prefixes.map(rest0 ++ _)

      def error[A](s: Str): A = this.error(s, elem.pos, Some(ks))

      seen.inlines.find(rest.is_child_of).foreach(ks =>
        error("Attempting to update an inline value"))

      val (inlines, tables) =
        elem match {
          case _: Parsers.Primitive =>
            (seen.inlines, seen.tables ++ implicitly_seen)
          case _: Parsers.Array =>
            if (seen_tables.contains(ks))
              error("Attempting to append with an inline array")
            (seen.inlines + rest, seen.tables ++ implicitly_seen)
          case _: Parsers.Inline_Table =>
            seen.tables.find(_.is_child_of(rest)).foreach(ks =>
              error("Attempting to add with an inline table"))
            (seen.inlines + rest, seen.tables ++ implicitly_seen)
          case _: Parsers.Table =>
            if (seen.tables.contains(rest))
              error("Attempting to define a table twice")
            (seen.inlines, seen.tables + rest)
          case _: Parsers.Array_Of_Tables => (Set.empty, Set.empty)
        }

      seen_tables += to -> Seen(inlines, tables)
    }

    def for_file(file: Path): Parse_Context = new Parse_Context(seen_tables, Some(file))

    def error[A](s: Str, pos: input.Position, key: Option[Keys] = None): A = {
      val key_msg = if_proper(key, " in table " + key.get)
      val file_msg = if_proper(file, " in " + file.get)
      isabelle.error(s + key_msg + " at line " + pos.line + file_msg)
    }

    def check_add_def(ks: Keys, defn: Parsers.Def): Unit = check_add(0, ks, defn)
    def check_add_value(ks0: Keys, ks1: Keys, v: Parsers.V): Unit =
      check_add(ks0.length - 1, ks0 ++ ks1, v)
  }

  object Parse_Context {
    case class Seen(inlines: Set[Keys], tables: Set[Keys])

    def apply(): Parse_Context =
      new Parse_Context(Map(Keys.empty -> Seen(Set.empty, Set.empty)))
  }

  def parse(s: Str, context: Parse_Context = Parse_Context()): Table = {
    val file =
      Parsers.phrase(Parsers.toml)(new Lexer.Scanner(Scan.char_reader(s + EofCh))) match {
        case Parsers.Success (toml, _) => toml
        case Parsers.Error(msg, next) => context.error("Error parsing toml: " + msg, next.pos)
        case Parsers.Failure (msg, next) =>
          context.error("Malformed TOML input: " + msg, next.pos)
      }

    def convert(ks0: Keys, ks1: Keys, v: Parsers.V): T = {
      def to_table(ks: Keys, t: T): Table =
        if (ks.length == 1) Table(ks.first.the_key -> t)
        else Table(ks.first.the_key -> to_table(ks.next, t))

      def to_toml(v: Parsers.V): (T, Set[Keys]) = v match {
        case Parsers.Primitive(t) => (t, Set.empty)
        case Parsers.Array(rep) => (Array(rep.map(to_toml(_)._1)), Set.empty)
        case Parsers.Inline_Table(elems) =>
          elems.find(e => elems.count(_._1 == e._1) > 1).foreach((ks, _) =>
            context.error(
              "Duplicate " + ks + " in inline table", v.pos, Some(ks0 ++ ks1)))

          val (tables, pfxs, key_spaces) =
            elems.map { (ks, v) =>
              val (t, keys) = to_toml(v)
              (to_table(ks, t), ks.prefixes, keys.map(ks ++ _) + ks)
            }.unzip3

          for {
            pfx <- pfxs
            if key_spaces.count(pfx.intersect(_).nonEmpty) > 1
          } context.error("Inline table not self-contained", v.pos, Some(ks0 ++ ks1))

          (tables.foldLeft(Table())(_ ++ _), pfxs.toSet.flatten ++ key_spaces.toSet.flatten)
      }
      context.check_add_value(ks0, ks1, v)
      to_toml(v)._1
    }

    def update(map: Table, ks0: Keys, value: T): Table = {
      def error[A](s: Str): A = context.error(s, ks0.pos, Some(ks0))

      def update_rec(hd: Keys, map: Table, ks: Keys): Table = {
        val updated =
          if (ks.length == 1) {
            map.any.get(ks.first.the_key) match {
              case Some(a: Array) =>
                value match {
                  case a2: Array => a ++ a2
                  case _ => error("Table conflicts with previous array of tables")
                }
              case Some(t: Table) => value match {
                case t2: Table =>
                  if (t.domain.intersect(t2.domain).nonEmpty)
                    error("Attempting to redefine existing value in super-table")
                  else t ++ t2
                case _ => error("Attempting to redefine a table")
              }
              case Some(_) => error("Attempting to redefine a value")
              case None => value
            }
          }
          else {
            val hd1 = hd ++ ks.first
            map.any.get(ks.first.the_key) match {
              case Some(t: Table) => update_rec(hd1, t, ks.next)
              case Some(a: Array) =>
                Array(a.table.values.dropRight(1) :+ update_rec(hd1, a.table.values.last, ks.next))
              case Some(_) => error("Attempting to redefine a value")
              case None => update_rec(hd1, Table(), ks.next)
            }
          }
        (map - ks.first.the_key) + (ks.first.the_key -> updated)
      }

      update_rec(Keys.empty, map, ks0)
    }

    def fold(elems: List[(Keys, T)]): Table =
      elems.foldLeft(Table()) { case (t0, (ks1, t1)) => update(t0, ks1, t1) }

    val t = fold(file.elems.map((ks, v) => (ks, convert(Keys.empty, ks, v))))
    file.defs.foldLeft(t) {
      case (t0, defn@Parsers.Table(ks0, elems)) =>
        context.check_add_def(ks0, defn)
        update(t0, ks0, fold(elems.map((ks, v) => (ks, convert(ks0, ks, v)))))
      case (t0, defn@Parsers.Array_Of_Tables(ks0, elems)) =>
        context.check_add_def(ks0, defn)
        update(t0, ks0, Array(fold(elems.map((ks, v) => (ks, convert(ks0, ks, v))))))
    }
  }

  def parse_files(files: Iterable[Path], context: Parse_Context = Parse_Context()): Table =
    files.foldLeft((Table(), context)) {
      case ((t, context0), file) =>
        val context = context0.for_file(file)
        (t ++ parse(File.read(file), context), context)
    }._1


  /* Format TOML */

  object Format {
    private def basic_string(s: Str): Str =
      "\"" + s.iterator.map {
        case '\b' => "\\b" case '\t' => "\\t" case '\n' => "\\n" case '\f' => "\\f"
        case '\r' => "\\r" case '"' => "\\\"" case '\\' => "\\\\" case c =>
        if (c <= '\u001f' || c == '\u007f') "\\u%04x".format(c.toInt) else c
      }.mkString + "\""

    private def multiline_basic_string(s: Str): Str =
      "\"\"\"\n" + s.iterator.map {
        case '\b' => "\\b" case '\t' => "\t" case '\n' => "\n" case '\f' => "\\f"
        case '\r' => "\r" case '"' => "\\\"" case '\\' => "\\\\" case c =>
          if (c <= '\u001f' || c == '\u007f') "\\u%04x".format(c.toInt) else c
      }.mkString.replace("\"\"\"", "\"\"\\\"") + "\"\"\""

    private def key(k: Key): Str = {
      val Bare_Key = """[A-Za-z0-9_-]+""".r
      k match {
        case Bare_Key() => k
        case _ => basic_string(k)
      }
    }

    private def keys(ks: List[Key]): Str = ks.map(key).mkString(".")

    private def inline(t: T, indent: Int = 0): Str = {
      val result = new StringBuilder

      result ++= Symbol.spaces(indent * 2)
      (t: @unchecked) match {
        case s: String =>
          if (s.rep.contains("\n") && s.rep.length > 20) result ++= multiline_basic_string(s.rep)
          else result ++= basic_string(s.rep)
        case a: Array =>
          if (a.is_empty) result ++= "[]"
          else {
            result ++= "[\n"
            a.any.values.foreach { elem =>
              result ++= inline(elem, indent + 1)
              result ++= ",\n"
            }
            result ++= Symbol.spaces(indent * 2)
            result += ']'
          }
        case table: Table =>
          if (table.is_empty) result ++= "{}"
          else {
            result ++= "{ "
            Library.separate(None, table.any.values.map(Some(_))).foreach {
              case None => result ++= ", "
              case Some((k, v)) =>
                result ++= key(k)
                result ++= " = "
                result ++= inline(v)
            }
            result ++= " }"
          }
        case Scalar(s) => result ++= s
      }
      result.toString()
    }

    def apply(toml: Table): Str = {
      val result = new StringBuilder

      def inline_values(path: List[Key], t: T): Unit =
        t match {
          case t: Table => t.any.values.foreach { case (k, v1) => inline_values(k :: path, v1) }
          case _ =>
            result ++= keys(path.reverse)
            result ++= " = "
            result ++= inline(t)
            result += '\n'
        }

      def is_inline(elem: T): Bool =
        elem match {
          case _: String | _: Integer | _: Float | _: Boolean | _: Offset_Date_Time |
               _: Local_Date_Time | _: Local_Date | _: Local_Time => true
          case a: Array => a.any.values.forall(is_inline)
          case _ => false
        }
      def is_table(elem: T): Bool = elem match { case _: Table => true case _ => false }

      def array(path: List[Key], a: Array): Unit =
        if (a.any.values.forall(is_inline) || !a.any.values.forall(is_table))
          inline_values(path.take(1), a)
        else a.table.values.foreach { t =>
          result ++= "\n[["
          result ++= keys(path.reverse)
          result ++= "]]\n"
          table(path, t, is_table_entry = true)
        }

      def table(path: List[Key], t: Table, is_table_entry: Bool = false): Unit = {
        val (values, nodes) = t.any.values.partition(kv => is_inline(kv._2))

        if (!is_table_entry && path.nonEmpty) {
          result ++= "\n["
          result ++= keys(path.reverse)
          result ++= "]\n"
        }

        values.foreach { case (k, v) => inline_values(List(k), v) }
        nodes.foreach {
          case (k, t: Table) => table(k :: path, t)
          case (k, arr: Array) => array(k :: path, arr)
          case _ =>
        }
      }

      table(Nil, toml)
      result.toString
    }
  }
}
