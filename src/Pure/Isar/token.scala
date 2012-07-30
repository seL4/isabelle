/*  Title:      Pure/Isar/token.scala
    Author:     Makarius

Outer token syntax for Isabelle/Isar.
*/

package isabelle


object Token
{
  /* tokens */

  object Kind extends Enumeration
  {
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
    val STRING = Value("string")
    val ALT_STRING = Value("back-quoted string")
    val VERBATIM = Value("verbatim text")
    val SPACE = Value("white space")
    val COMMENT = Value("comment text")
    val UNPARSED = Value("unparsed input")
  }


  /* token reader */

  class Position(val line: Int, val file: String) extends scala.util.parsing.input.Position
  {
    def column = 0
    def lineContents = ""
    override def toString =
      if (file == "") ("line " + line.toString)
      else ("line " + line.toString + " of " + quote(file))

    def advance(token: Token): Position =
    {
      var n = 0
      for (c <- token.content if c == '\n') n += 1
      if (n == 0) this else new Position(line + n, file)
    }
  }

  abstract class Reader extends scala.util.parsing.input.Reader[Token]

  private class Token_Reader(tokens: List[Token], val pos: Position) extends Reader
  {
    def first = tokens.head
    def rest = new Token_Reader(tokens.tail, pos.advance(first))
    def atEnd = tokens.isEmpty
  }

  def reader(tokens: List[Token], file: String = ""): Reader =
    new Token_Reader(tokens, new Position(1, file))
}


sealed case class Token(val kind: Token.Kind.Value, val source: String)
{
  def is_command: Boolean = kind == Token.Kind.COMMAND
  def is_operator: Boolean = kind == Token.Kind.KEYWORD && !Symbol.is_ascii_identifier(source)
  def is_delimited: Boolean =
    kind == Token.Kind.STRING ||
    kind == Token.Kind.ALT_STRING ||
    kind == Token.Kind.VERBATIM ||
    kind == Token.Kind.COMMENT
  def is_ident: Boolean = kind == Token.Kind.IDENT
  def is_string: Boolean = kind == Token.Kind.STRING
  def is_nat: Boolean = kind == Token.Kind.NAT
  def is_float: Boolean = kind == Token.Kind.FLOAT
  def is_name: Boolean =
    kind == Token.Kind.IDENT ||
    kind == Token.Kind.SYM_IDENT ||
    kind == Token.Kind.STRING ||
    kind == Token.Kind.NAT
  def is_xname: Boolean = is_name || kind == Token.Kind.LONG_IDENT
  def is_text: Boolean = is_xname || kind == Token.Kind.VERBATIM
  def is_space: Boolean = kind == Token.Kind.SPACE
  def is_comment: Boolean = kind == Token.Kind.COMMENT
  def is_proper: Boolean = !is_space && !is_comment
  def is_unparsed: Boolean = kind == Token.Kind.UNPARSED

  def is_begin: Boolean = kind == Token.Kind.KEYWORD && source == "begin"
  def is_end: Boolean = kind == Token.Kind.COMMAND && source == "end"

  def content: String =
    if (kind == Token.Kind.STRING) Scan.Lexicon.empty.quoted_content("\"", source)
    else if (kind == Token.Kind.ALT_STRING) Scan.Lexicon.empty.quoted_content("`", source)
    else if (kind == Token.Kind.VERBATIM) Scan.Lexicon.empty.verbatim_content(source)
    else if (kind == Token.Kind.COMMENT) Scan.Lexicon.empty.comment_content(source)
    else source

  def text: (String, String) =
    if (kind == Token.Kind.COMMAND && source == ";") ("terminator", "")
    else (kind.toString, source)
}

