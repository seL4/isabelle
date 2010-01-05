/*  Title:      Pure/Thy/thy_syntax.scala
    Author:     Makarius

Superficial theory syntax: command spans.
*/

package isabelle


class Thy_Syntax
{
  private val parser = new Outer_Parse.Parser
  {
    override def filter_proper = false

    val command_span: Parser[Span] =
    {
      val whitespace = token("white space", tok => tok.is_space || tok.is_comment)
      val command = token("command keyword", _.is_command)
      val body = not(rep(whitespace) ~ (command | eof)) ~> not_eof
      command ~ rep(body) ^^ { case x ~ ys => x :: ys } | rep1(whitespace) | rep1(body)
    }
  }

  type Span = List[Outer_Lex.Token]

  def parse_spans(toks: List[Outer_Lex.Token]): List[Span] =
  {
    import parser._

    parse(rep(command_span), Outer_Lex.reader(toks)) match {
      case Success(spans, rest) if rest.atEnd => spans
      case bad => error(bad.toString)
    }
  }
}
