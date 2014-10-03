/*  Title:      Pure/Tools/bibtex.scala
    Author:     Makarius

Some support for bibtex files.
*/

package isabelle


import scala.util.parsing.input.{Reader, CharSequenceReader}
import scala.util.parsing.combinator.RegexParsers


object Bibtex
{
  /** content **/

  val months = List(
    "jan",
    "feb",
    "mar",
    "apr",
    "may",
    "jun",
    "jul",
    "aug",
    "sep",
    "oct",
    "nov",
    "dec")

  val commands = List("preamble", "string")

  sealed case class Entry(
    kind: String,
    required: List[String],
    optional_crossref: List[String],
    optional: List[String])
  {
    def fields: List[String] = required ::: optional_crossref ::: optional
    def template: String =
      "@" + kind + "{,\n" + fields.map(x => "  " + x + " = {},\n").mkString + "}\n"
  }

  val entries: List[Entry] =
    List(
      Entry("Article",
        List("author", "title"),
        List("journal", "year"),
        List("volume", "number", "pages", "month", "note")),
      Entry("InProceedings",
        List("author", "title"),
        List("booktitle", "year"),
        List("editor", "volume", "number", "series", "pages", "month", "address",
          "organization", "publisher", "note")),
      Entry("InCollection",
        List("author", "title", "booktitle"),
        List("publisher", "year"),
        List("editor", "volume", "number", "series", "type", "chapter", "pages",
          "edition", "month", "address", "note")),
      Entry("InBook",
        List("author", "editor", "title", "chapter"),
        List("publisher", "year"),
        List("volume", "number", "series", "type", "address", "edition", "month", "pages", "note")),
      Entry("Proceedings",
        List("title", "year"),
        List(),
        List("booktitle", "editor", "volume", "number", "series", "address", "month",
          "organization", "publisher", "note")),
      Entry("Book",
        List("author", "editor", "title"),
        List("publisher", "year"),
        List("volume", "number", "series", "address", "edition", "month", "note")),
      Entry("Booklet",
        List("title"),
        List(),
        List("author", "howpublished", "address", "month", "year", "note")),
      Entry("PhdThesis",
        List("author", "title", "school", "year"),
        List(),
        List("type", "address", "month", "note")),
      Entry("MastersThesis",
        List("author", "title", "school", "year"),
        List(),
        List("type", "address", "month", "note")),
      Entry("TechReport",
        List("author", "title", "institution", "year"),
        List(),
        List("type", "number", "address", "month", "note")),
      Entry("Manual",
        List("title"),
        List(),
        List("author", "organization", "address", "edition", "month", "year", "note")),
      Entry("Unpublished",
        List("author", "title", "note"),
        List(),
        List("month", "year")),
      Entry("Misc",
        List(),
        List(),
        List("author", "title", "howpublished", "month", "year", "note")))



  /** tokens and chunks **/

  object Token
  {
    object Kind extends Enumeration
    {
      val KEYWORD = Value("keyword")
      val NAT = Value("natural number")
      val IDENT = Value("identifier")
      val STRING = Value("string")
      val SPACE = Value("white space")
      val ERROR = Value("bad input")
    }
  }

  sealed case class Token(kind: Token.Kind.Value, val source: String)
  {
    def is_space: Boolean = kind == Token.Kind.SPACE
    def is_error: Boolean = kind == Token.Kind.ERROR
  }

  abstract class Chunk { def size: Int; def kind: String = "" }
  case class Ignored(source: String) extends Chunk { def size: Int = source.size }
  case class Malformed(source: String) extends Chunk { def size: Int = source.size }
  case class Item(tokens: List[Token]) extends Chunk
  {
    def size: Int = (0 /: tokens)({ case (n, token) => n + token.source.size })

    private val content: (String, List[Token]) =
      tokens match {
        case Token(Token.Kind.KEYWORD, "@") :: body
        if !body.isEmpty && !body.exists(_.is_error) =>
          (body.init.filterNot(_.is_space), body.last) match {
            case (Token(Token.Kind.IDENT, id) :: Token(Token.Kind.KEYWORD, "{") :: toks,
                  Token(Token.Kind.KEYWORD, "}")) => (id, toks)
            case (Token(Token.Kind.IDENT, id) :: Token(Token.Kind.KEYWORD, "(") :: toks,
                  Token(Token.Kind.KEYWORD, ")")) => (id, toks)
            case _ => ("", Nil)
          }
        case _ => ("", Nil)
      }
    override def kind: String = content._1
    def content_tokens: List[Token] = content._2

    def is_wellformed: Boolean = kind != ""

    def name: String =
      content_tokens match {
        case Token(Token.Kind.IDENT, name) :: _ if is_wellformed => name
        case _ => ""
      }
  }



  /** parsing **/

  // context of partial line-oriented scans
  abstract class Line_Context
  case class Delimited(quoted: Boolean, depth: Int) extends Line_Context
  val Finished = Delimited(false, 0)

  private def token(kind: Token.Kind.Value)(source: String): Token = Token(kind, source)
  private def keyword(source: String): Token = Token(Token.Kind.KEYWORD, source)


  // See also http://ctan.org/tex-archive/biblio/bibtex/base/bibtex.web
  // module @<Scan for and process a \.{.bib} command or database entry@>.

  object Parsers extends RegexParsers
  {
    /* white space and comments */

    override val whiteSpace = "".r

    private val space = """[ \t\n\r]+""".r ^^ token(Token.Kind.SPACE)
    private val strict_space = """[ \t]+""".r ^^ token(Token.Kind.SPACE)

    private val ignored =
      rep1("""(?mi)([^@]+|@[ \t\n\r]*comment)""".r) ^^ { case ss => Ignored(ss.mkString) }


    /* delimited string: outermost "..." or {...} and body with balanced {...} */

    private def delimited_depth(delim: Delimited): Parser[(String, Delimited)] =
      new Parser[(String, Delimited)]
      {
        require(if (delim.quoted) delim.depth > 0 else delim.depth >= 0)

        def apply(in: Input) =
        {
          val start = in.offset
          val end = in.source.length

          var i = start
          var q = delim.quoted
          var d = delim.depth
          var finished = false
          while (!finished && i < end) {
            val c = in.source.charAt(i)
            if (c == '"' && d == 0) { i += 1; d = 1; q = true }
            else if (c == '"' && d == 1) { i += 1; d = 0; q = false; finished = true }
            else if (c == '{') { i += 1; d += 1 }
            else if (c == '}' && d > 0) { i += 1; d -= 1; if (d == 0) finished = true }
            else if (d > 0) i += 1
            else finished = true
          }
          if (i == start) Failure("bad input", in)
          else
            Success((in.source.subSequence(start, i).toString,
              Delimited(q, d)), in.drop(i - start))
        }
      }.named("delimited_depth")

    private def delimited: Parser[String] =
      delimited_depth(Finished) ^? { case (x, delim) if delim == Finished => x }

    private def delimited_line(ctxt: Line_Context): Parser[(String, Line_Context)] =
    {
      ctxt match {
        case delim: Delimited => delimited_depth(delim)
        case _ => failure("")
      }
    }

    private val recover_delimited: Parser[String] =
      delimited_depth(Finished) ^^ (_._1)

    private val delimited_token =
      delimited ^^ token(Token.Kind.STRING) |
      recover_delimited ^^ token(Token.Kind.ERROR)


    /* other tokens */

    private val at = "@" ^^ keyword
    private val left_brace = "{" ^^ keyword
    private val right_brace = "}" ^^ keyword
    private val left_paren = "(" ^^ keyword
    private val right_paren = ")" ^^ keyword

    private val nat = "[0-9]+".r ^^ token(Token.Kind.NAT)

    private val ident =
      """[\x21-\x7f&&[^"#%'(),={}0-9]][\x21-\x7f&&[^"#%'(),={}]]*""".r ^^ token(Token.Kind.IDENT)


    /* chunks */

    private val item_start =
      at ~ rep(strict_space) ~ ident ~ rep(strict_space) ^^
        { case a ~ b ~ c ~ d => List(a) ::: b ::: List(c) ::: d }

    private val body_token = delimited_token | ("[=#,]".r ^^ keyword | (nat | (ident | space)))

    private val item =
      (item_start ~ left_brace ~ rep(body_token) ~ opt(right_brace) |
       item_start ~ left_paren ~ rep(body_token) ~ opt(right_paren)) ^^
        { case a ~ b ~ c ~ d => Item(a ::: List(b) ::: c ::: d.toList) }

    private val recover_item = "(?m)@[^@]+".r ^^ (s => Malformed(s))

    val chunks: Parser[List[Chunk]] = rep(ignored | (item | recover_item))
  }

  def parse(input: CharSequence): List[Chunk] =
  {
    val in: Reader[Char] = new CharSequenceReader(input)
    Parsers.parseAll(Parsers.chunks, in) match {
      case Parsers.Success(result, _) => result
      case _ => error("Unexpected failure to parse input:\n" + input.toString)
    }
  }
}

