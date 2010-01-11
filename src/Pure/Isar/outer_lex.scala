/*  Title:      Pure/Isar/outer_lex.scala
    Author:     Makarius

Outer lexical syntax for Isabelle/Isar.
*/

package isabelle


object Outer_Lex
{
  /* tokens */

  object Token_Kind extends Enumeration
  {
    val COMMAND = Value("command")
    val KEYWORD = Value("keyword")
    val IDENT = Value("identifier")
    val LONG_IDENT = Value("long identifier")
    val SYM_IDENT = Value("symbolic identifier")
    val VAR = Value("schematic variable")
    val TYPE_IDENT = Value("type variable")
    val TYPE_VAR = Value("schematic type variable")
    val NAT = Value("number")
    val STRING = Value("string")
    val ALT_STRING = Value("back-quoted string")
    val VERBATIM = Value("verbatim text")
    val SPACE = Value("white space")
    val COMMENT = Value("comment text")
    val BAD_INPUT = Value("bad input")
    val UNPARSED = Value("unparsed input")
  }

  sealed case class Token(val kind: Token_Kind.Value, val source: String)
  {
    def is_command: Boolean = kind == Token_Kind.COMMAND
    def is_delimited: Boolean =
      kind == Token_Kind.STRING ||
      kind == Token_Kind.ALT_STRING ||
      kind == Token_Kind.VERBATIM ||
      kind == Token_Kind.COMMENT
    def is_name: Boolean =
      kind == Token_Kind.IDENT ||
      kind == Token_Kind.SYM_IDENT ||
      kind == Token_Kind.STRING ||
      kind == Token_Kind.NAT
    def is_xname: Boolean = is_name || kind == Token_Kind.LONG_IDENT
    def is_text: Boolean = is_xname || kind == Token_Kind.VERBATIM
    def is_space: Boolean = kind == Token_Kind.SPACE
    def is_comment: Boolean = kind == Token_Kind.COMMENT
    def is_ignored: Boolean = is_space || is_comment
    def is_unparsed: Boolean = kind == Token_Kind.UNPARSED

    def content: String =
      if (kind == Token_Kind.STRING) Scan.Lexicon.empty.quoted_content("\"", source)
      else if (kind == Token_Kind.ALT_STRING) Scan.Lexicon.empty.quoted_content("`", source)
      else if (kind == Token_Kind.VERBATIM) Scan.Lexicon.empty.verbatim_content(source)
      else if (kind == Token_Kind.COMMENT) Scan.Lexicon.empty.comment_content(source)
      else source

    def text: (String, String) =
      if (kind == Token_Kind.COMMAND && source == ";") ("terminator", "")
      else (kind.toString, source)
  }


  /* token reader */

  class Line_Position(val line: Int) extends scala.util.parsing.input.Position
  {
    def column = 0
    def lineContents = ""
    override def toString = line.toString

    def advance(token: Token): Line_Position =
    {
      var n = 0
      for (c <- token.content if c == '\n') n += 1
      if (n == 0) this else new Line_Position(line + n)
    }
  }

  abstract class Reader extends scala.util.parsing.input.Reader[Token]

  private class Token_Reader(tokens: List[Token], val pos: Line_Position) extends Reader
  {
    def first = tokens.head
    def rest = new Token_Reader(tokens.tail, pos.advance(first))
    def atEnd = tokens.isEmpty
  }

  def reader(tokens: List[Token]): Reader = new Token_Reader(tokens, new Line_Position(1))
}

