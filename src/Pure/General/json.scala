/*  Title:      Pure/General/json.scala
    Author:     Makarius

Support for JSON: https://www.json.org/.

See also http://seriot.ch/parsing_json.php "Parsing JSON is a Minefield".
*/

package isabelle


import scala.util.matching.Regex
import scala.util.parsing.combinator
import scala.util.parsing.combinator.lexical.Scanners
import scala.util.parsing.input.CharArrayReader.EofCh


object JSON {
  type T = Any
  type S = String

  object Object {
    type Entry = (String, JSON.T)

    type T = Map[String, JSON.T]
    val empty: Object.T = Map.empty

    def apply(entries: Entry*): Object.T = entries.toMap

    def unapply(obj: Any): Option[Object.T] =
      obj match {
        case m: Map[_, _] if m.keySet.forall(_.isInstanceOf[String]) =>
          Some(m.asInstanceOf[Object.T])
        case _ => None
      }

    def parse(s: S): Object.T =
      unapply(JSON.parse(s)).getOrElse(error("Bad JSON object " + quote(s)))
  }


  /* lexer */

  enum Kind { case KEYWORD, STRING, NUMBER, ERROR }

  sealed case class Token(kind: Kind, text: String) {
    def is_keyword: Boolean = kind == Kind.KEYWORD
    def is_keyword(name: String): Boolean = kind == Kind.KEYWORD && text == name
    def is_string: Boolean = kind == Kind.STRING
    def is_number: Boolean = kind == Kind.NUMBER
    def is_error: Boolean = kind == Kind.ERROR
  }

  object Lexer extends Scanners with Scan.Parsers {
    override type Elem = Char
    type Token = JSON.Token

    def errorToken(msg: String): Token = Token(Kind.ERROR, msg)

    val white_space: String = " \t\n\r"
    override val whiteSpace: Regex = ("[" + white_space + "]+").r
    def whitespace: Parser[Any] = many(character(white_space.contains(_)))

    val letter: Parser[String] = one(character(Symbol.is_ascii_letter))
    val letters1: Parser[String] = many1(character(Symbol.is_ascii_letter))

    def digits: Parser[String] = many(character(Symbol.is_ascii_digit))
    def digits1: Parser[String] = many1(character(Symbol.is_ascii_digit))


    /* keyword */

    def keyword: Parser[Token] =
      (letters1 | one(character("{}[],:".contains(_)))) ^^ (s => Token(Kind.KEYWORD, s))


    /* string */

    def string: Parser[Token] =
      '\"' ~> rep(string_body) <~ '\"' ^^ (cs => Token(Kind.STRING, cs.mkString))

    def string_body: Parser[Char] =
      elem("", c => c > '\u001f' && c != '\"' && c != '\\' && c != EofCh) | '\\' ~> string_escape

    def string_escape: Parser[Char] =
      elem("", "\"\\/".contains(_)) |
      elem("", "bfnrt".contains(_)) ^^
        { case 'b' => '\b' case 'f' => '\f' case 'n' => '\n' case 'r' => '\r' case 't' => '\t' } |
      'u' ~> repeated(character(Symbol.is_ascii_hex), 4, 4) ^^
        (s => Integer.parseInt(s, 16).toChar)

    def string_failure: Parser[Token] = '\"' ~> failure("Unterminated string")


    /* number */

    def number: Parser[Token] =
      opt("-") ~ number_body ~ opt(letter) ^^ {
        case a ~ b ~ None => Token(Kind.NUMBER, a.getOrElse("") + b)
        case a ~ b ~ Some(c) =>
          errorToken("Invalid number format: " + quote(a.getOrElse("") + b + c))
      }

    def number_body: Parser[String] =
      (zero | positive) ~ opt(number_fract) ~ opt(number_exp) ^^
        { case a ~ b ~ c => a + b.getOrElse("") + c.getOrElse("") }

    def number_fract: Parser[String] = "." ~ digits1 ^^ { case a ~ b => a + b }

    def number_exp: Parser[String] =
      one(character("eE".contains(_))) ~ maybe(character("-+".contains(_))) ~ digits1 ^^
        { case a ~ b ~ c => a + b + c }

    def zero: Parser[String] = one(character(c => c == '0'))
    def nonzero: Parser[String] = one(character(c => c != '0' && Symbol.is_ascii_digit(c)))
    def positive: Parser[String] = nonzero ~ digits ^^ { case a ~ b => a + b }


    /* token */

    def token: Parser[Token] =
      keyword | (string | (string_failure | (number | failure("Illegal character"))))
  }


  /* parser */

  trait Parsers extends combinator.Parsers {
    type Elem = Token

    def $$$(name: String): Parser[Token] = elem(name, _.is_keyword(name))
    def string: Parser[String] = elem("string", _.is_string) ^^ (_.text)
    def number: Parser[Double] = elem("number", _.is_number) ^^ (tok => tok.text.toDouble)

    def json_object: Parser[Object.T] =
      $$$("{") ~>
        repsep(string ~ ($$$(":") ~> json_value) ^^ { case a ~ b => (a, b) }, $$$(",")) <~
      $$$("}") ^^ (_.toMap)

    def json_array: Parser[List[T]] =
      $$$("[") ~> repsep(json_value, $$$(",")) <~ $$$("]")

    def json_value: Parser[T] =
      json_object | (json_array | (number | (string |
        ($$$("true") ^^^ true | ($$$("false") ^^^ false | ($$$("null") ^^^ null))))))

    def parse(input: CharSequence, strict: Boolean): T = {
      val scanner = new Lexer.Scanner(Scan.char_reader(input))
      val result = phrase(if (strict) json_object | json_array else json_value)(scanner)
      (result : @unchecked) match {
        case Success(json, _) => json
        case NoSuccess(_, next) => error("Malformed JSON input at " + next.pos)
      }
    }
  }

  object Parsers extends Parsers


  /* standard format */

  def parse(s: S, strict: Boolean = true): T = Parsers.parse(s, strict)

  object Format {
    def unapply(s: S): Option[T] =
      try { Some(parse(s, strict = false)) }
      catch { case ERROR(_) => None }

    def apply(json: T): S = bytes(json).text

    private def bytes_string(s: String, builder: Bytes.Builder): Unit = {
      builder += "\""
      builder +=
        s.iterator.map {
          case '"' => "\\\""
          case '\\' => "\\\\"
          case '\b' => "\\b"
          case '\f' => "\\f"
          case '\n' => "\\n"
          case '\r' => "\\r"
          case '\t' => "\\t"
          case c =>
            if (c <= '\u001f' || c >= '\u007f' && c <= '\u009f') "\\u%04x".format(c.toInt)
            else c
        }.mkString
      builder += "\""
    }

    private def bytes_atom(x: T, builder: Bytes.Builder): Boolean =
      x match {
        case null => builder += "null"; true
        case _: Int | _ : Long | _: Boolean => builder += x.toString; true
        case n: Double =>
          val i = n.toLong
          builder += (if (i.toDouble == n) i.toString else n.toString)
          true
        case s: String => bytes_string(s, builder); true
        case _ => false
      }

    def bytes(json: T, hint: Long = 0L): Bytes =
      Bytes.Builder.use(hint = hint) { builder =>
        def output(x: T): Unit = {
          if (!bytes_atom(x, builder)) {
            x match {
              case Object(obj) =>
                builder += "{"
                Library.separate(None, obj.toList.map(Some(_))).foreach({
                  case None => builder += ","
                  case Some((x, y)) =>
                    bytes_string(x, builder)
                    builder += ":"
                    output(y)
                })
                builder += "}"
              case list: List[T] =>
                builder += "["
                Library.separate(None, list.map(Some(_))).foreach({
                  case None => builder += ","
                  case Some(x) => output(x)
                })
                builder += "]"
              case _ => error("Bad JSON value: " + x.toString)
            }
          }
        }

        output(json)
      }

    private def pretty_atom(x: T): Option[XML.Tree] = {
      val builder = new Bytes.Builder()
      val ok = bytes_atom(x, builder)
      if (ok) Some(XML.Text(builder.done().text)) else None
    }

    private def pretty_string(s: String): XML.Tree =
      XML.Text(Bytes.Builder.use()(bytes_string(s, _)).text)

    private def pretty_tree(x: T): XML.Tree =
      x match {
        case Object(obj) =>
          Pretty.`enum`(
            for ((x, y) <- obj.toList)
              yield Pretty.block(List(pretty_string(x), XML.Text(":"), Pretty.brk(1), pretty(y))),
            bg = "{", en = "}", indent = 1)
        case list: List[T] =>
          Pretty.`enum`(list.map(pretty), bg = "[", en = "]", indent = 1)
        case _ => error("Bad JSON value: " + x.toString)
      }

    def pretty(x: T): XML.Tree = pretty_atom(x) getOrElse pretty_tree(x)

    def pretty_print(x: T, margin: Int = Pretty.default_margin.toInt): JSON.S =
      Pretty.string_of(List(pretty(x)), margin = margin.toDouble)
  }


  /* typed values */

  object Value {
    object UUID {
      def unapply(json: T): Option[isabelle.UUID.T] =
        json match {
          case x: java.lang.String => isabelle.UUID.unapply(x)
          case _ => None
        }
    }

    object String {
      def unapply(json: T): Option[java.lang.String] =
        json match {
          case x: java.lang.String => Some(x)
          case _ => None
        }
    }

    object String0 {
      def unapply(json: T): Option[java.lang.String] =
        json match {
          case null => Some("")
          case x: java.lang.String => Some(x)
          case _ => None
        }
    }

    object Double {
      def unapply(json: T): Option[scala.Double] =
        json match {
          case x: scala.Double => Some(x)
          case x: scala.Long => Some(x.toDouble)
          case x: scala.Int => Some(x.toDouble)
          case _ => None
        }
    }

    object Long {
      def unapply(json: T): Option[scala.Long] =
        json match {
          case x: scala.Double if x.toLong.toDouble == x => Some(x.toLong)
          case x: scala.Long => Some(x)
          case x: scala.Int => Some(x.toLong)
          case _ => None
        }
    }

    object Int {
      def unapply(json: T): Option[scala.Int] =
        json match {
          case x: scala.Double if x.toInt.toDouble == x => Some(x.toInt)
          case x: scala.Long if x.toInt.toLong == x => Some(x.toInt)
          case x: scala.Int => Some(x)
          case _ => None
        }
    }

    object Boolean {
      def unapply(json: T): Option[scala.Boolean] =
        json match {
          case x: scala.Boolean => Some(x)
          case _ => None
        }
    }

    object List {
      def unapply[A](json: T, unapply: T => Option[A]): Option[List[A]] =
        json match {
          case xs: List[T] =>
            val ys = xs.map(unapply)
            if (ys.forall(_.isDefined)) Some(ys.map(_.get)) else None
          case _ => None
        }
    }

    object Seconds {
      def unapply(json: T): Option[Time] =
        Double.unapply(json).map(Time.seconds)
    }
  }


  /* object values */

  def optional(entry: (String, Option[T])): Object.T =
    entry match {
      case (name, Some(x)) => Object(name -> x)
      case (_, None) => Object.empty
    }

  def value(obj: T, name: String): Option[T] =
    obj match {
      case Object(m) => m.get(name)
      case _ => None
    }

  def value[A](obj: T, name: String, unapply: T => Option[A]): Option[A] =
    for {
      json <- value(obj, name)
      x <- unapply(json)
    } yield x

  def array(obj: T, name: String): Option[List[T]] =
    value(obj, name) match {
      case Some(a: List[T]) => Some(a)
      case _ => None
    }

  def value_default[A](obj: T, name: String, unapply: T => Option[A], default: => A): Option[A] =
    value(obj, name) match {
      case None => Some(default)
      case Some(json) => unapply(json)
    }

  def uuid(obj: T, name: String): Option[UUID.T] =
    value(obj, name, Value.UUID.unapply)

  def string(obj: T, name: String): Option[String] =
    value(obj, name, Value.String.unapply)
  def string_default(obj: T, name: String, default: => String = ""): Option[String] =
    value_default(obj, name, Value.String.unapply, default)

  def string0(obj: T, name: String): Option[String] =
    value(obj, name, Value.String0.unapply)
  def string0_default(obj: T, name: String, default: => String = ""): Option[String] =
    value_default(obj, name, Value.String0.unapply, default)

  def double(obj: T, name: String): Option[Double] =
    value(obj, name, Value.Double.unapply)
  def double_default(obj: T, name: String, default: => Double = 0.0): Option[Double] =
    value_default(obj, name, Value.Double.unapply, default)

  def long(obj: T, name: String): Option[Long] =
    value(obj, name, Value.Long.unapply)
  def long_default(obj: T, name: String, default: => Long = 0): Option[Long] =
    value_default(obj, name, Value.Long.unapply, default)

  def int(obj: T, name: String): Option[Int] =
    value(obj, name, Value.Int.unapply)
  def int_default(obj: T, name: String, default: => Int = 0): Option[Int] =
    value_default(obj, name, Value.Int.unapply, default)

  def bool(obj: T, name: String): Option[Boolean] =
    value(obj, name, Value.Boolean.unapply)
  def bool_default(obj: T, name: String, default: => Boolean = false): Option[Boolean] =
    value_default(obj, name, Value.Boolean.unapply, default)

  def list[A](obj: T, name: String, unapply: T => Option[A]): Option[List[A]] =
    value(obj, name, Value.List.unapply(_, unapply))
  def list_default[A](obj: T, name: String, unapply: T => Option[A], default: => List[A] = Nil)
    : Option[List[A]] = value_default(obj, name, Value.List.unapply(_, unapply), default)

  def strings(obj: T, name: String): Option[List[String]] =
    list(obj, name, JSON.Value.String.unapply)
  def strings_default(obj: T, name: String, default: => List[String] = Nil): Option[List[String]] =
    list_default(obj, name, JSON.Value.String.unapply, default)

  def seconds(obj: T, name: String): Option[Time] =
    value(obj, name, Value.Seconds.unapply)
  def seconds_default(obj: T, name: String, default: => Time = Time.zero): Option[Time] =
    value_default(obj, name, Value.Seconds.unapply, default)
}
