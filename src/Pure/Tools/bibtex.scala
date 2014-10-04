/*  Title:      Pure/Tools/bibtex.scala
    Author:     Makarius

Some support for bibtex files.
*/

package isabelle


import scala.collection.mutable
import scala.util.parsing.input.{Reader, CharSequenceReader}
import scala.util.parsing.combinator.RegexParsers


object Bibtex
{
  /** content **/

  private val months = List(
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
  def is_month(s: String): Boolean = months.contains(s.toLowerCase)

  private val commands = List("preamble", "string")
  def is_command(s: String): Boolean = commands.contains(s.toLowerCase)

  sealed case class Entry(
    kind: String,
    required: List[String],
    optional_crossref: List[String],
    optional_other: List[String])
  {
    def is_required(s: String): Boolean = required.contains(s)
    def is_optional(s: String): Boolean =
      optional_crossref.contains(s) || optional_other.contains(s)

    def fields: List[String] = required ::: optional_crossref ::: optional_other
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

  def get_entry(kind: String): Option[Entry] =
    entries.find(entry => entry.kind.toLowerCase == kind.toLowerCase)

  def is_entry(kind: String): Boolean = get_entry(kind).isDefined



  /** tokens and chunks **/

  object Token
  {
    object Kind extends Enumeration
    {
      val COMMAND = Value("command")
      val ENTRY = Value("entry")
      val KEYWORD = Value("keyword")
      val NAT = Value("natural number")
      val STRING = Value("string")
      val IDENT = Value("identifier")
      val IGNORED = Value("ignored")
      val ERROR = Value("bad input")
    }
  }

  sealed case class Token(kind: Token.Kind.Value, val source: String)
  {
    def is_kind: Boolean =
      kind == Token.Kind.COMMAND ||
      kind == Token.Kind.ENTRY ||
      kind == Token.Kind.IDENT
    def is_ignored: Boolean = kind == Token.Kind.IGNORED
    def is_malformed: Boolean = kind == Token.Kind.ERROR
  }

  case class Chunk(kind: String, tokens: List[Token])
  {
    val source = tokens.map(_.source).mkString

    private val content: Option[List[Token]] =
      tokens match {
        case Token(Token.Kind.KEYWORD, "@") :: body if !body.isEmpty =>
          (body.init.filterNot(_.is_ignored), body.last) match {
            case (tok :: Token(Token.Kind.KEYWORD, "{") :: toks, Token(Token.Kind.KEYWORD, "}"))
            if tok.is_kind => Some(toks)

            case (tok :: Token(Token.Kind.KEYWORD, "(") :: toks, Token(Token.Kind.KEYWORD, ")"))
            if tok.is_kind => Some(toks)

            case _ => None
          }
        case _ => None
      }

    def name: String =
      content match {
        case Some(Token(Token.Kind.IDENT, a) :: _) => a
        case _ => ""
      }

    def is_ignored: Boolean = kind == "" && tokens.forall(_.is_ignored)
    def is_malformed: Boolean = kind == "" || tokens.exists(_.is_malformed)
    def is_command: Boolean =
      Bibtex.is_command(kind) && name != "" && content.isDefined && !is_malformed
    def is_entry: Boolean =
      Bibtex.is_entry(kind) && name != "" && content.isDefined && !is_malformed
  }



  /** parsing **/

  // context of partial line-oriented scans
  abstract class Line_Context
  case object Ignored_Context extends Line_Context
  case class Item_Context(kind: String, delim: Delimited, right: String) extends Line_Context
  case class Delimited(quoted: Boolean, depth: Int)
  val Closed = Delimited(false, 0)

  private def token(kind: Token.Kind.Value)(source: String): Token = Token(kind, source)
  private def keyword(source: String): Token = Token(Token.Kind.KEYWORD, source)


  // See also http://ctan.org/tex-archive/biblio/bibtex/base/bibtex.web
  // module @<Scan for and process a \.{.bib} command or database entry@>.

  object Parsers extends RegexParsers
  {
    /* white space and comments */

    override val whiteSpace = "".r

    private val space = """[ \t\n\r]+""".r ^^ token(Token.Kind.IGNORED)
    private val strict_space = """[ \t]+""".r ^^ token(Token.Kind.IGNORED)


    /* ignored material */

    private val ignored: Parser[Chunk] =
      rep1("""(?mi)([^@]+|@[ \t]*comment)""".r) ^^ {
        case ss => Chunk("", List(Token(Token.Kind.IGNORED, ss.mkString))) }


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
          else {
            val s = in.source.subSequence(start, i).toString
            Success((s, Delimited(q, d)), in.drop(i - start))
          }
        }
      }.named("delimited_depth")

    private def delimited: Parser[Token] =
      delimited_depth(Closed) ^?
        { case (s, delim) if delim == Closed => Token(Token.Kind.STRING, s) }

    private def delimited_line(ctxt: Line_Context): Parser[(Chunk, Line_Context)] =
    {
      ctxt match {
        case Item_Context(kind, delim, right) =>
          delimited_depth(delim) ^^ { case (s, delim1) =>
            (Chunk(kind, List(Token(Token.Kind.STRING, s))), Item_Context(kind, delim1, right)) }
        case _ => failure("")
      }
    }

    private def recover_delimited: Parser[Token] =
      """(?m)["{][^@]+""".r ^^ token(Token.Kind.ERROR)


    /* other tokens */

    private val at = "@" ^^ keyword
    private val left_brace = "{" ^^ keyword
    private val right_brace = "}" ^^ keyword
    private val left_paren = "(" ^^ keyword
    private val right_paren = ")" ^^ keyword

    private val nat = "[0-9]+".r ^^ token(Token.Kind.NAT)

    private val identifier =
      """[\x21-\x7f&&[^"#%'(),={}0-9]][\x21-\x7f&&[^"#%'(),={}]]*""".r

    private val ident = identifier ^^ token(Token.Kind.IDENT)

    val other_token = "[=#,]".r ^^ keyword | (nat | (ident | space))


    /* items: command or entry */

    private val item_kind =
      identifier ^^ { case a =>
        val kind =
          if (is_command(a)) Token.Kind.COMMAND
          else if (is_entry(a)) Token.Kind.ENTRY
          else Token.Kind.IDENT
        Token(kind, a)
      }

    private val item_start: Parser[(String, List[Token])] =
      at ~ rep(strict_space) ~ item_kind ~ rep(strict_space) ^^
        { case a ~ b ~ c ~ d => (c.source, List(a) ::: b ::: List(c) ::: d) }

    private val item_body =
      delimited | (recover_delimited | other_token)

    private val item: Parser[Chunk] =
      (item_start ~ left_brace ~ rep(item_body) ~ opt(right_brace) |
       item_start ~ left_paren ~ rep(item_body) ~ opt(right_paren)) ^^
        { case (kind, a) ~ b ~ c ~ d => Chunk(kind, a ::: List(b) ::: c ::: d.toList) }

    private val recover_item: Parser[Chunk] =
      at ~ "(?m)[^@]*".r ^^ { case a ~ b => Chunk("", List(a, Token(Token.Kind.ERROR, b))) }


    /* chunks */

    val chunk: Parser[Chunk] = ignored | (item | recover_item)

    def chunk_line(ctxt: Line_Context): Parser[(Chunk, Line_Context)] =
    {
      ctxt match {
        case Ignored_Context =>
          ignored ^^ { case a => (a, ctxt) } |
          item_start ~ (left_brace | left_paren) ^^
            { case (kind, a) ~ b =>
                val right = if (b.source == "{") "}" else ")"
                (Chunk(kind, a ::: List(b)), Item_Context(kind, Closed, right)) } |
          recover_item ^^ { case a => (a, Ignored_Context) }
        case Item_Context(kind, delim, right) =>
          if (delim.depth > 0)
            delimited_line(ctxt)
          else {
            delimited_line(ctxt) |
            other_token ^^ { case a => (Chunk(kind, List(a)), ctxt) } |
            right ^^ { case a => (Chunk(kind, List(keyword(a))), Ignored_Context) }
          }
        case _ => failure("")
      }
    }
  }


  /* parse */

  def parse(input: CharSequence): List[Chunk] =
  {
    val in: Reader[Char] = new CharSequenceReader(input)
    Parsers.parseAll(Parsers.rep(Parsers.chunk), in) match {
      case Parsers.Success(result, _) => result
      case _ => error("Unexpected failure to parse input:\n" + input.toString)
    }
  }

  def parse_line(input: CharSequence, context: Line_Context): (List[Chunk], Line_Context) =
  {
    var in: Reader[Char] = new CharSequenceReader(input)
    val chunks = new mutable.ListBuffer[Chunk]
    var ctxt = context
    while (!in.atEnd) {
      Parsers.parse(Parsers.chunk_line(ctxt), in) match {
        case Parsers.Success((x, c), rest) => { chunks += x; ctxt = c; in = rest }
        case Parsers.NoSuccess(_, rest) =>
          error("Unepected failure to parse input:\n" + rest.source.toString)
      }
    }
    (chunks.toList, ctxt)
  }
}

