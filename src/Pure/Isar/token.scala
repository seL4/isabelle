/*  Title:      Pure/Isar/token.scala
    Author:     Makarius

Outer token syntax for Isabelle/Isar.
*/

package isabelle


import scala.collection.mutable
import scala.util.parsing.input


object Token
{
  /* tokens */

  object Kind extends Enumeration
  {
    /*immediate source*/
    val COMMAND = Value("command")
    val KEYWORD = Value("keyword")
    val IDENT = Value("identifier")
    val LONG_IDENT = Value("long identifier")
    val SYM_IDENT = Value("symbolic identifier")
    val VAR = Value("schematic variable")
    val TYPE_IDENT = Value("type variable")
    val TYPE_VAR = Value("schematic type variable")
    val NAT = Value("natural number")
    val FLOAT = Value("floating-point number")
    val SPACE = Value("white space")
    /*delimited content*/
    val STRING = Value("string")
    val ALT_STRING = Value("back-quoted string")
    val VERBATIM = Value("verbatim text")
    val CARTOUCHE = Value("text cartouche")
    val CONTROL = Value("control cartouche")
    val INFORMAL_COMMENT = Value("informal comment")
    val FORMAL_COMMENT = Value("formal comment")
    /*special content*/
    val ERROR = Value("bad input")
    val UNPARSED = Value("unparsed input")
  }


  /* parsers */

  object Parsers extends Parsers

  trait Parsers extends Scan.Parsers with Comment.Parsers
  {
    private def delimited_token: Parser[Token] =
    {
      val string = quoted("\"") ^^ (x => Token(Token.Kind.STRING, x))
      val alt_string = quoted("`") ^^ (x => Token(Token.Kind.ALT_STRING, x))
      val verb = verbatim ^^ (x => Token(Token.Kind.VERBATIM, x))
      val cmt = comment ^^ (x => Token(Token.Kind.INFORMAL_COMMENT, x))
      val formal_cmt = comment_cartouche ^^ (x => Token(Token.Kind.FORMAL_COMMENT, x))
      val cart = cartouche ^^ (x => Token(Token.Kind.CARTOUCHE, x))
      val ctrl = control_cartouche ^^ (x => Token(Token.Kind.CONTROL, x))

      string | (alt_string | (verb | (cmt | (formal_cmt | (cart | ctrl)))))
    }

    private def other_token(keywords: Keyword.Keywords): Parser[Token] =
    {
      val letdigs1 = many1(Symbol.is_letdig)
      val sub = one(s => s == Symbol.sub_decoded || s == Symbol.sub)
      val id =
        one(Symbol.is_letter) ~
          (rep(letdigs1 | (sub ~ letdigs1 ^^ { case x ~ y => x + y })) ^^ (_.mkString)) ^^
        { case x ~ y => x + y }

      val nat = many1(Symbol.is_digit)
      val natdot = nat ~ "." ~ nat ^^ { case x ~ y ~ z => x + y + z }
      val id_nat = id ~ opt("." ~ nat) ^^ { case x ~ Some(y ~ z) => x + y + z case x ~ None => x }

      val ident = id ~ rep("." ~> id) ^^
        { case x ~ Nil => Token(Token.Kind.IDENT, x)
          case x ~ ys => Token(Token.Kind.LONG_IDENT, (x :: ys).mkString(".")) }

      val var_ = "?" ~ id_nat ^^ { case x ~ y => Token(Token.Kind.VAR, x + y) }
      val type_ident = "'" ~ id ^^ { case x ~ y => Token(Token.Kind.TYPE_IDENT, x + y) }
      val type_var = "?'" ~ id_nat ^^ { case x ~ y => Token(Token.Kind.TYPE_VAR, x + y) }
      val nat_ = nat ^^ (x => Token(Token.Kind.NAT, x))
      val float =
        ("-" ~ natdot ^^ { case x ~ y => x + y } | natdot) ^^ (x => Token(Token.Kind.FLOAT, x))

      val sym_ident =
        (many1(Symbol.is_symbolic_char) | one(sym => Symbol.is_symbolic(sym))) ^^
        (x => Token(Token.Kind.SYM_IDENT, x))

      val keyword =
        literal(keywords.minor) ^^ (x => Token(Token.Kind.KEYWORD, x)) |||
        literal(keywords.major) ^^ (x => Token(Token.Kind.COMMAND, x))

      val space = many1(Symbol.is_blank) ^^ (x => Token(Token.Kind.SPACE, x))

      val recover_delimited =
        (recover_quoted("\"") |
          (recover_quoted("`") |
            (recover_verbatim |
              (recover_cartouche | recover_comment)))) ^^ (x => Token(Token.Kind.ERROR, x))

      val bad = one(_ => true) ^^ (x => Token(Token.Kind.ERROR, x))

      space | (recover_delimited |
        (((ident | (var_ | (type_ident | (type_var | (float | (nat_ | sym_ident)))))) |||
          keyword) | bad))
    }

    def token(keywords: Keyword.Keywords): Parser[Token] =
      delimited_token | other_token(keywords)

    def token_line(keywords: Keyword.Keywords, ctxt: Scan.Line_Context)
      : Parser[(Token, Scan.Line_Context)] =
    {
      val string =
        quoted_line("\"", ctxt) ^^ { case (x, c) => (Token(Token.Kind.STRING, x), c) }
      val alt_string =
        quoted_line("`", ctxt) ^^ { case (x, c) => (Token(Token.Kind.ALT_STRING, x), c) }
      val verb = verbatim_line(ctxt) ^^ { case (x, c) => (Token(Token.Kind.VERBATIM, x), c) }
      val cart = cartouche_line(ctxt) ^^ { case (x, c) => (Token(Token.Kind.CARTOUCHE, x), c) }
      val cmt = comment_line(ctxt) ^^ { case (x, c) => (Token(Token.Kind.INFORMAL_COMMENT, x), c) }
      val formal_cmt =
        comment_cartouche_line(ctxt) ^^ { case (x, c) => (Token(Token.Kind.FORMAL_COMMENT, x), c) }
      val other = other_token(keywords) ^^ { case x => (x, Scan.Finished) }

      string | (alt_string | (verb | (cart | (cmt | (formal_cmt | other)))))
    }
  }


  /* explode */

  def explode(keywords: Keyword.Keywords, inp: CharSequence): List[Token] =
    Parsers.parseAll(Parsers.rep(Parsers.token(keywords)), Scan.char_reader(inp)) match {
      case Parsers.Success(tokens, _) => tokens
      case _ => error("Unexpected failure of tokenizing input:\n" + inp.toString)
    }

  def explode_line(keywords: Keyword.Keywords, inp: CharSequence, context: Scan.Line_Context)
    : (List[Token], Scan.Line_Context) =
  {
    var in: input.Reader[Char] = Scan.char_reader(inp)
    val toks = new mutable.ListBuffer[Token]
    var ctxt = context
    while (!in.atEnd) {
      Parsers.parse(Parsers.token_line(keywords, ctxt), in) match {
        case Parsers.Success((x, c), rest) => toks += x; ctxt = c; in = rest
        case Parsers.NoSuccess(_, rest) =>
          error("Unexpected failure of tokenizing input:\n" + rest.source.toString)
      }
    }
    (toks.toList, ctxt)
  }

  val newline: Token = explode(Keyword.Keywords.empty, "\n").head


  /* embedded */

  def read_embedded(keywords: Keyword.Keywords, inp: CharSequence): Option[Token] =
    explode(keywords, inp) match {
      case List(tok) if tok.is_embedded => Some(tok)
      case _ => None
    }


  /* names */

  def read_name(keywords: Keyword.Keywords, inp: CharSequence): Option[Token] =
    explode(keywords, inp) match {
      case List(tok) if tok.is_name => Some(tok)
      case _ => None
    }

  def quote_name(keywords: Keyword.Keywords, name: String): String =
    if (read_name(keywords, name).isDefined) name
    else quote(name.replace("\"", "\\\""))


  /* plain antiquotation (0 or 1 args) */

  def read_antiq_arg(keywords: Keyword.Keywords, inp: CharSequence): Option[(String, Option[String])] =
    explode(keywords, inp).filter(_.is_proper) match {
      case List(t) if t.is_name => Some(t.content, None)
      case List(t1, t2) if t1.is_name && t2.is_embedded => Some(t1.content, Some(t2.content))
      case _ => None
    }


  /* implode */

  def implode(toks: List[Token]): String =
    toks match {
      case List(tok) => tok.source
      case _ => toks.map(_.source).mkString
    }


  /* token reader */

  object Pos
  {
    val none: Pos = new Pos(0, 0, "", "")
    val start: Pos = new Pos(1, 1, "", "")
    def file(file: String): Pos = new Pos(1, 1, file, "")
    def id(id: String): Pos = new Pos(0, 1, "", id)
    val command: Pos = id(Markup.COMMAND)
  }

  final class Pos private[Token](
      val line: Int,
      val offset: Symbol.Offset,
      val file: String,
      val id: String)
    extends input.Position
  {
    def column = 0
    def lineContents = ""

    def advance(token: Token): Pos = advance(token.source)
    def advance(source: String): Pos =
    {
      var line1 = line
      var offset1 = offset
      for (s <- Symbol.iterator(source)) {
        if (line1 > 0 && Symbol.is_newline(s)) line1 += 1
        if (offset1 > 0) offset1 += 1
      }
      if (line1 == line && offset1 == offset) this
      else new Pos(line1, offset1, file, id)
    }

    private def position(end_offset: Symbol.Offset): Position.T =
      (if (line > 0) Position.Line(line) else Nil) :::
      (if (offset > 0) Position.Offset(offset) else Nil) :::
      (if (end_offset > 0) Position.End_Offset(end_offset) else Nil) :::
      (if (file != "") Position.File(file) else Nil) :::
      (if (id != "") Position.Id_String(id) else Nil)

    def position(): Position.T = position(0)
    def position(token: Token): Position.T = position(advance(token).offset)
    def position(source: String): Position.T = position(advance(source).offset)

    override def toString: String = Position.here(position(), delimited = false)
  }

  abstract class Reader extends input.Reader[Token]

  private class Token_Reader(tokens: List[Token], val pos: Pos) extends Reader
  {
    def first: Token = tokens.head
    def rest: Token_Reader = new Token_Reader(tokens.tail, pos.advance(first))
    def atEnd: Boolean = tokens.isEmpty
  }

  def reader(tokens: List[Token], start: Token.Pos): Reader =
    new Token_Reader(tokens, start)
}


sealed case class Token(kind: Token.Kind.Value, source: String)
{
  def is_command: Boolean = kind == Token.Kind.COMMAND
  def is_command(name: String): Boolean = kind == Token.Kind.COMMAND && source == name
  def is_keyword: Boolean = kind == Token.Kind.KEYWORD
  def is_keyword(name: String): Boolean = kind == Token.Kind.KEYWORD && source == name
  def is_keyword(name: Char): Boolean =
    kind == Token.Kind.KEYWORD && source.length == 1 && source(0) == name
  def is_delimiter: Boolean = is_keyword && !Symbol.is_ascii_identifier(source)
  def is_ident: Boolean = kind == Token.Kind.IDENT
  def is_sym_ident: Boolean = kind == Token.Kind.SYM_IDENT
  def is_string: Boolean = kind == Token.Kind.STRING
  def is_nat: Boolean = kind == Token.Kind.NAT
  def is_float: Boolean = kind == Token.Kind.FLOAT
  def is_name: Boolean =
    kind == Token.Kind.IDENT ||
    kind == Token.Kind.LONG_IDENT ||
    kind == Token.Kind.SYM_IDENT ||
    kind == Token.Kind.STRING ||
    kind == Token.Kind.NAT
  def is_embedded: Boolean = is_name ||
    kind == Token.Kind.CARTOUCHE ||
    kind == Token.Kind.VAR ||
    kind == Token.Kind.TYPE_IDENT ||
    kind == Token.Kind.TYPE_VAR
  def is_text: Boolean = is_embedded || kind == Token.Kind.VERBATIM
  def is_space: Boolean = kind == Token.Kind.SPACE
  def is_informal_comment: Boolean = kind == Token.Kind.INFORMAL_COMMENT
  def is_formal_comment: Boolean = kind == Token.Kind.FORMAL_COMMENT
  def is_marker: Boolean =
    kind == Token.Kind.FORMAL_COMMENT &&
    (source.startsWith(Symbol.marker) || source.startsWith(Symbol.marker_decoded))
  def is_comment: Boolean = is_informal_comment || is_formal_comment
  def is_ignored: Boolean = is_space || is_informal_comment
  def is_proper: Boolean = !is_space && !is_comment
  def is_error: Boolean = kind == Token.Kind.ERROR
  def is_unparsed: Boolean = kind == Token.Kind.UNPARSED

  def is_unfinished: Boolean = is_error &&
   (source.startsWith("\"") ||
    source.startsWith("`") ||
    source.startsWith("{*") ||
    source.startsWith("(*") ||
    source.startsWith(Symbol.open) ||
    source.startsWith(Symbol.open_decoded))

  def is_open_bracket: Boolean = is_keyword && Word.open_brackets.exists(is_keyword)
  def is_close_bracket: Boolean = is_keyword && Word.close_brackets.exists(is_keyword)

  def is_begin: Boolean = is_keyword("begin")
  def is_end: Boolean = is_command("end")
  def is_begin_or_command: Boolean = is_begin || is_command

  def symbol_length: Symbol.Offset = Symbol.iterator(source).length

  def content: String =
    if (kind == Token.Kind.STRING) Scan.Parsers.quoted_content("\"", source)
    else if (kind == Token.Kind.ALT_STRING) Scan.Parsers.quoted_content("`", source)
    else if (kind == Token.Kind.VERBATIM) Scan.Parsers.verbatim_content(source)
    else if (kind == Token.Kind.CARTOUCHE) Scan.Parsers.cartouche_content(source)
    else if (kind == Token.Kind.INFORMAL_COMMENT) Scan.Parsers.comment_content(source)
    else if (kind == Token.Kind.FORMAL_COMMENT) Comment.content(source)
    else source

  def is_system_name: Boolean =
  {
    val s = content
    is_name && Path.is_wellformed(s) &&
      !s.exists(Symbol.is_ascii_blank) &&
      !Path.is_reserved(s)
  }
}
