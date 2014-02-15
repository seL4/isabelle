/*  Title:      Pure/ML/ml_lex.scala
    Author:     Makarius

Lexical syntax for SML.
*/

package isabelle


import scala.collection.mutable
import scala.util.parsing.input.{Reader, CharSequenceReader}


object ML_Lex
{
  /** tokens **/

  object Kind extends Enumeration
  {
    val KEYWORD = Value("keyword")
    val IDENT = Value("identifier")
    val LONG_IDENT = Value("long identifier")
    val TYPE_VAR = Value("type variable")
    val WORD = Value("word")
    val INT = Value("integer")
    val REAL = Value("real")
    val CHAR = Value("character")
    val STRING = Value("quoted string")
    val SPACE = Value("white space")
    val COMMENT = Value("comment text")
    val ERROR = Value("bad input")
  }

  sealed case class Token(val kind: Kind.Value, val source: String)
  {
    def is_operator: Boolean = kind == Kind.KEYWORD && !Symbol.is_ascii_identifier(source)
  }



  /** parsers **/

  case object ML_String extends Scan.Context

  private val lexicon =
    Scan.Lexicon("#", "(", ")", ",", "->", "...", ":", ":>", ";", "=",
      "=>", "[", "]", "_", "{", "|", "}", "abstype", "and", "andalso", "as",
      "case", "datatype", "do", "else", "end", "eqtype", "exception", "fn",
      "fun", "functor", "handle", "if", "in", "include", "infix", "infixr",
      "let", "local", "nonfix", "of", "op", "open", "orelse", "raise", "rec",
      "sharing", "sig", "signature", "struct", "structure", "then", "type",
      "val", "where", "while", "with", "withtype")

  private object Parsers extends Scan.Parsers
  {
    /* string material */

    private val blanks = many(character(Symbol.is_ascii_blank))
    private val blanks1 = many1(character(Symbol.is_ascii_blank))

    private val gap = "\\" ~ blanks1 ~ "\\" ^^ { case x ~ y ~ z => x + y + z }
    private val gap_start = "\\" ~ blanks ~ """\z""".r ^^ { case x ~ y ~ _ => x + y }

    private val escape =
      one(character("\"\\abtnvfr".contains(_))) |
      "^" ~ one(character(c => '@' <= c && c <= '_')) ^^ { case x ~ y => x + y } |
      repeated(character(Symbol.is_ascii_digit), 3, 3)

    private val str =
      one(character(c => c != '"' && c != '\\' && ' ' <= c && c <= '~')) |
      "\\" ~ escape ^^ { case x ~ y => x + y }


    /* ML char -- without gaps */

    private val ml_char: Parser[Token] =
      "#\"" ~ str ~ "\"" ^^ { case x ~ y ~ z => Token(Kind.CHAR, x + y + z) }

    private val recover_ml_char: Parser[String] =
      "#\"" ~ opt(str) ^^ { case x ~ Some(y) => x + y case x ~ None => x }


    /* ML string */

    private val ml_string_body: Parser[String] =
      rep(gap | str) ^^ (_.mkString)

    private val recover_ml_string: Parser[String] =
      "\"" ~ ml_string_body ^^ { case x ~ y => x + y }

    private val ml_string: Parser[Token] =
      "\"" ~ ml_string_body ~ "\"" ^^ { case x ~ y ~ z => Token(Kind.STRING, x + y + z) }

    private def ml_string_context(ctxt: Scan.Context): Parser[(Token, Scan.Context)] =
    {
      def result(x: String, c: Scan.Context) = (Token(Kind.STRING, x), c)

      ctxt match {
        case Scan.Finished =>
          "\"" ~ ml_string_body ~ ("\"" | gap_start) ^^
            { case x ~ y ~ z => result(x + y + z, if (z == "\"") Scan.Finished else ML_String) }
        case ML_String =>
          blanks ~ opt_term("\\" ~ ml_string_body ~ ("\"" | gap_start)) ^^
            { case x ~ Some(y ~ z ~ w) =>
                result(x + y + z + w, if (w == "\"") Scan.Finished else ML_String)
              case x ~ None => result(x, ML_String) }
        case _ => failure("")
      }
    }


    /* ML comment */

    private val ml_comment: Parser[Token] =
      comment ^^ (x => Token(Kind.COMMENT, x))

    private def ml_comment_context(ctxt: Scan.Context): Parser[(Token, Scan.Context)] =
      comment_context(ctxt) ^^ { case (x, c) => (Token(Kind.COMMENT, x), c) }


    /* delimited token */

    private def delimited_token: Parser[Token] =
      ml_char | (ml_string | ml_comment)

    private val recover_delimited: Parser[Token] =
      (recover_ml_char | (recover_ml_string | recover_comment)) ^^ (x => Token(Kind.ERROR, x))


    private def other_token: Parser[Token] =
    {
      /* identifiers */

      val letdigs = many(character(Symbol.is_ascii_letdig))

      val alphanumeric =
        one(character(Symbol.is_ascii_letter)) ~ letdigs ^^ { case x ~ y => x + y }

      val symbolic = many1(character("!#$%&*+-/:<=>?@\\^`|~".contains(_)))

      val ident = (alphanumeric | symbolic) ^^ (x => Token(Kind.IDENT, x))

      val long_ident =
        rep1(alphanumeric ~ "." ^^ { case x ~ y => x + y }) ~
          (alphanumeric | (symbolic | "=")) ^^
          { case x ~ y => Token(Kind.LONG_IDENT, x.mkString + y) }

      val type_var = "'" ~ letdigs ^^ { case x ~ y => Token(Kind.TYPE_VAR, x + y) }


      /* numerals */

      val dec = many1(character(Symbol.is_ascii_digit))
      val hex = many1(character(Symbol.is_ascii_hex))
      val sign = opt("~") ^^ { case Some(x) => x case None => "" }
      val decint = sign ~ dec ^^ { case x ~ y => x + y }
      val exp = ("E" | "e") ~ decint ^^ { case x ~ y => x + y }

      val word =
        ("0wx" ~ hex ^^ { case x ~ y => x + y } | "0w" ~ dec ^^ { case x ~ y => x + y }) ^^
          (x => Token(Kind.WORD, x))

      val int =
        sign ~ ("0x" ~ hex ^^ { case x ~ y => x + y } | dec) ^^
          { case x ~ y => Token(Kind.INT, x + y) }

      val real =
        (decint ~ "." ~ dec ~ (opt(exp) ^^ { case Some(x) => x case None => "" }) ^^
          { case x ~ y ~ z ~ w => x + y + z + w } |
         decint ~ exp ^^ { case x ~ y => x + y }) ^^ (x => Token(Kind.REAL, x))


      /* main */

      val space = blanks1 ^^ (x => Token(Kind.SPACE, x))

      val keyword = literal(lexicon) ^^ (x => Token(Kind.KEYWORD, x))

      val bad = one(_ => true) ^^ (x => Token(Kind.ERROR, x))

      space | (recover_delimited |
        (((word | (real | (int | (long_ident | (ident | type_var))))) ||| keyword) | bad))
    }


    /* token */

    def token: Parser[Token] = delimited_token | other_token

    def token_context(ctxt: Scan.Context): Parser[(Token, Scan.Context)] =
    {
      val other = (ml_char | other_token) ^^ (x => (x, Scan.Finished))

      ml_string_context(ctxt) | (ml_comment_context(ctxt) | other)
    }
  }


  /* tokenize */

  def tokenize(input: CharSequence): List[Token] =
  {
    Parsers.parseAll(Parsers.rep(Parsers.token), new CharSequenceReader(input)) match {
      case Parsers.Success(tokens, _) => tokens
      case _ => error("Unexpected failure of tokenizing input:\n" + input.toString)
    }
  }

  def tokenize_context(input: CharSequence, context: Scan.Context): (List[Token], Scan.Context) =
  {
    var in: Reader[Char] = new CharSequenceReader(input)
    val toks = new mutable.ListBuffer[Token]
    var ctxt = context
    while (!in.atEnd) {
      Parsers.parse(Parsers.token_context(ctxt), in) match {
        case Parsers.Success((x, c), rest) => { toks += x; ctxt = c; in = rest }
        case Parsers.NoSuccess(_, rest) =>
          error("Unexpected failure of tokenizing input:\n" + rest.source.toString)
      }
    }
    (toks.toList, ctxt)
  }
}

