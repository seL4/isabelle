/*  Title:      Pure/Thy/thy_syntax.scala
    Author:     Makarius

Superficial theory syntax: command spans.
*/

package isabelle


object Thy_Syntax
{
  private val parser = new Parse.Parser
  {
    override def filter_proper = false

    val command_span: Parser[Span] =
    {
      val whitespace = token("white space", _.is_ignored)
      val command = token("command keyword", _.is_command)
      val body = not(rep(whitespace) ~ (command | eof)) ~> not_eof
      command ~ rep(body) ^^ { case x ~ ys => x :: ys } | rep1(whitespace) | rep1(body)
    }
  }

  type Span = List[Token]

  def parse_spans(toks: List[Token]): List[Span] =
  {
    import parser._

    parse(rep(command_span), Token.reader(toks)) match {
      case Success(spans, rest) if rest.atEnd => spans
      case bad => error(bad.toString)
    }
  }
}
