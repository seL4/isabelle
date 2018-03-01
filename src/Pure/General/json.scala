/*  Title:      Pure/General/json.scala
    Author:     Makarius

Support for JSON.
*/

package isabelle


import scala.util.parsing.combinator.Parsers
import scala.util.parsing.combinator.lexical.Scanners
import scala.util.parsing.input.CharArrayReader.EofCh


object JSON
{
  type T = Any
  type S = String

  type Object = Map[String, T]
  val empty: Object = Map.empty


  /* lexer */

  object Kind extends Enumeration
  {
    val KEYWORD, STRING, NUMBER, ERROR = Value
  }

  sealed case class Token(kind: Kind.Value, text: String)
  {
    def is_keyword: Boolean = kind == Kind.KEYWORD
    def is_keyword(name: String): Boolean = kind == Kind.KEYWORD && text == name
    def is_string: Boolean = kind == Kind.STRING
    def is_number: Boolean = kind == Kind.NUMBER
    def is_error: Boolean = kind == Kind.ERROR
  }

  object Lexer extends Scanners with Scan.Parsers
  {
    override type Elem = Char
    type Token = JSON.Token

    def errorToken(msg: String): Token = Token(Kind.ERROR, msg)

    val white_space: String = " \t\n\r"
    override val whiteSpace = ("[" + white_space + "]+").r
    def whitespace: Parser[Any] = many(character(white_space.contains(_)))

    val letter: Parser[String] = one(character(Symbol.is_ascii_letter(_)))
    val letters1: Parser[String] = many1(character(Symbol.is_ascii_letter(_)))

    def digits: Parser[String] = many(character(Symbol.is_ascii_digit(_)))
    def digits1: Parser[String] = many1(character(Symbol.is_ascii_digit(_)))


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
      'u' ~> repeated(character("0123456789abcdefABCDEF".contains(_)), 4, 4) ^^
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

    def zero = one(character(c => c == '0'))
    def nonzero = one(character(c => c != '0' && Symbol.is_ascii_digit(c)))
    def positive: Parser[String] = nonzero ~ digits ^^ { case a ~ b => a + b }


    /* token */

    def token: Parser[Token] =
      keyword | (string | (string_failure | (number | failure("Illegal character"))))
  }


  /* parser */

  trait Parser extends Parsers
  {
    type Elem = Token

    def $$$(name: String): Parser[Token] = elem(name, _.is_keyword(name))
    def string: Parser[String] = elem("string", _.is_string) ^^ (_.text)
    def number: Parser[Double] = elem("number", _.is_number) ^^ (tok => tok.text.toDouble)

    def json_object: Parser[Object] =
      $$$("{") ~>
        repsep(string ~ ($$$(":") ~> json_value) ^^ { case a ~ b => (a, b) }, $$$(",")) <~
      $$$("}") ^^ (_.toMap)

    def json_array: Parser[List[T]] =
      $$$("[") ~> repsep(json_value, $$$(",")) <~ $$$("]")

    def json_value: Parser[T] =
      json_object | (json_array | (number | (string |
        ($$$("true") ^^^ true | ($$$("false") ^^^ false | ($$$("null") ^^^ null))))))

    def parse(input: CharSequence, strict: Boolean): T =
    {
      val scanner = new Lexer.Scanner(Scan.char_reader(input))
      phrase(if (strict) json_object | json_array else json_value)(scanner) match {
        case Success(json, _) => json
        case NoSuccess(_, next) => error("Malformed JSON input at " + next.pos)
      }
    }
  }

  object Parser extends Parser


  /* standard format */

  def parse(s: S, strict: Boolean = true): T = Parser.parse(s, strict)

  object Format
  {
    def unapply(s: S): Option[T] =
      try { Some(parse(s, strict = false)) }
      catch { case ERROR(_) => None }

    def apply(json: T): S =
    {
      val result = new StringBuilder

      def string(s: String)
      {
        result += '"'
        result ++=
          s.iterator.map {
            case '"'  => "\\\""
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
        result += '"'
      }

      def array(list: List[T])
      {
        result += '['
        Library.separate(None, list.map(Some(_))).foreach({
          case None => result += ','
          case Some(x) => json_format(x)
        })
        result += ']'
      }

      def object_(obj: Object)
      {
        result += '{'
        Library.separate(None, obj.toList.map(Some(_))).foreach({
          case None => result += ','
          case Some((x, y)) =>
            string(x)
            result += ':'
            json_format(y)
        })
        result += '}'
      }

      def json_format(x: T)
      {
        x match {
          case null => result ++= "null"
          case _: Int | _: Long | _: Boolean => result ++= x.toString
          case n: Double =>
            val i = n.toLong
            result ++= (if (i.toDouble == n) i.toString else n.toString)
          case s: String => string(s)
          case obj: Map[_, _] if obj.keySet.forall(_.isInstanceOf[String]) =>
            object_(obj.asInstanceOf[Object])
          case list: List[T] => array(list)
          case _ => error("Bad JSON value: " + x.toString)
        }
      }

      json_format(json)
      result.toString
    }
  }


  /* numbers */

  object Number
  {
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
  }


  /* object values */

  def optional(entry: (String, Option[T])): Object =
    entry match {
      case (name, Some(x)) => Map(name -> x)
      case (_, None) => empty
    }

  def value(obj: T, name: String): Option[T] =
    obj match {
      case m: Map[_, _] if m.keySet.forall(_.isInstanceOf[String]) =>
        m.asInstanceOf[Object].get(name)
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

  def array[A](obj: T, name: String, unapply: T => Option[A]): Option[List[A]] =
    for {
      a0 <- array(obj, name)
      a = a0.map(unapply(_))
      if a.forall(_.isDefined)
    } yield a.map(_.get)

  def string(obj: T, name: String): Option[String] =
    value(obj, name) match {
      case Some(x: String) => Some(x)
      case _ => None
    }

  def double(obj: T, name: String): Option[Double] =
    value(obj, name, Number.Double.unapply)

  def long(obj: T, name: String): Option[Long] =
    value(obj, name, Number.Long.unapply)

  def int(obj: T, name: String): Option[Int] =
    value(obj, name, Number.Int.unapply)

  def bool(obj: T, name: String): Option[Boolean] =
    value(obj, name) match {
      case Some(x: Boolean) => Some(x)
      case _ => None
    }
}
