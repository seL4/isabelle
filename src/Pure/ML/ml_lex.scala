/*  Title:      Pure/ML/ml_lex.scala
    Author:     Makarius

Lexical syntax for SML.
*/

package isabelle

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



  /** parsers **/

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

    private val blanks1 = many1(character(Symbol.is_ascii_blank))

    private val escape =
      one(character("\"\\abtnvfr".contains(_))) |
      "^" ~ one(character(c => '@' <= c && c <= '_')) ^^ { case x ~ y => x + y } |
      repeated(character(Symbol.is_ascii_digit), 3, 3)

    private val str =
      one(character(c => c != '"' && c != '\\' && ' ' <= c && c <= '~')) |
      "\\" ~ escape ^^ { case x ~ y => x + y }

    private val gap = "\\" ~ blanks1 ~ "\\" ^^ { case x ~ y ~ z => x + y + z }
    private val gaps = rep(gap) ^^ (_.mkString)


    /* delimited token */

    private def delimited_token: Parser[Token] =
    {
      val char =
        "#\"" ~ gaps ~ str ~ gaps ~ "\"" ^^
        { case u ~ v ~ x ~ y ~ z => Token(Kind.CHAR, u + v + x + y + z) }

      val string =
        "\"" ~ (rep(gap | str) ^^ (_.mkString)) ~ "\"" ^^
        { case x ~ y ~ z => Token(Kind.STRING, x + y + z) }

      val cmt = comment ^^ (x => Token(Kind.COMMENT, x))

      char | (string | cmt)
    }

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


      /* recover delimited */

      val recover_char =
        "#\"" ~ gaps ~ (opt(str ~ gaps) ^^ { case Some(x ~ y) => x + y case None => "" }) ^^
          { case x ~ y ~ z => x + y + z }

      val recover_string =
        "\"" ~ (rep(gap | str) ^^ (_.mkString)) ^^ { case x ~ y => x + y }

      val recover_delimited =
        (recover_char | (recover_string | recover_comment)) ^^ (x => Token(Kind.ERROR, x))


      /* token */

      val space = blanks1 ^^ (x => Token(Kind.SPACE, x))

      val keyword = literal(lexicon) ^^ (x => Token(Kind.KEYWORD, x))

      val bad = one(_ => true) ^^ (x => Token(Kind.ERROR, x))

      space | (recover_delimited |
        (((word | (real | (int | (long_ident | (ident | type_var))))) ||| keyword) | bad))
    }

    def token: Parser[Token] = delimited_token | other_token
  }

  def tokenize(input: CharSequence): List[Token] =
  {
    Parsers.parseAll(Parsers.rep(Parsers.token), new CharSequenceReader(input)) match {
      case Parsers.Success(tokens, _) => tokens
      case _ => error("Unexpected failure of tokenizing input:\n" + input.toString)
    }
  }
}

