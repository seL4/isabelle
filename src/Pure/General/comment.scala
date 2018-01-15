/*  Title:      Pure/General/comment.scala
    Author:     Makarius

Formal comments.
*/

package isabelle


object Comment
{
  object Kind extends Enumeration
  {
    val COMMENT = Value("formal comment")
    val CANCEL = Value("canceled text")
    val LATEX = Value("embedded LaTeX")
  }

  lazy val symbols: Set[Symbol.Symbol] =
    Set(Symbol.comment, Symbol.comment_decoded,
      Symbol.cancel, Symbol.cancel_decoded,
      Symbol.latex, Symbol.latex_decoded)

  def symbols_blanks(sym: Symbol.Symbol): Boolean = Symbol.is_comment(sym)

  def content(source: String): String =
  {
    def err(): Nothing = error("Malformed formal comment: " + quote(source))

    Symbol.explode(source) match {
      case sym :: rest if symbols_blanks(sym) =>
        val body = if (symbols_blanks(sym)) rest.dropWhile(Symbol.is_blank) else rest
        try { Scan.Parsers.cartouche_content(body.mkString) }
        catch { case ERROR(_) => err() }
      case _ => err()
    }
  }

  trait Parsers extends Scan.Parsers
  {
   def comment_prefix: Parser[String] =
     one(symbols_blanks) ~ many(Symbol.is_blank) ^^ { case a ~ b => a + b.mkString } |
     one(symbols)

   def comment_cartouche: Parser[String] =
      comment_prefix ~ cartouche ^^ { case a ~ b => a + b }

    def comment_cartouche_line(ctxt: Scan.Line_Context): Parser[(String, Scan.Line_Context)] =
    {
      def cartouche_context(d: Int): Scan.Line_Context =
        if (d == 0) Scan.Finished else Scan.Cartouche_Comment(d)

      ctxt match {
        case Scan.Finished =>
          comment_prefix ~ opt(cartouche_depth(0)) ^^ {
            case a ~ None => (a, Scan.Comment_Prefix(a))
            case a ~ Some((c, d)) => (a + c, cartouche_context(d)) }
        case Scan.Comment_Prefix(a) if symbols_blanks(a) =>
          many1(Symbol.is_blank) ~ opt(cartouche_depth(0)) ^^ {
            case b ~ None => (b.mkString, Scan.Comment_Prefix(a))
            case b ~ Some((c, d)) => (b.mkString + c, cartouche_context(d)) } |
          cartouche_depth(0) ^^ { case (c, d) => (c, cartouche_context(d)) }
        case Scan.Comment_Prefix(_) =>
          cartouche_depth(0) ^^ { case (c, d) => (c, cartouche_context(d)) }
        case Scan.Cartouche_Comment(depth) =>
          cartouche_depth(depth) ^^ { case (c, d) => (c, cartouche_context(d)) }
        case _ => failure("")
      }
    }
  }
}
