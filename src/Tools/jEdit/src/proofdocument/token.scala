/*
 * Document tokens as text ranges
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.proofdocument


object Token {
  object Kind extends Enumeration
  {
    val COMMAND_START = Value("COMMAND_START")
    val COMMENT = Value("COMMENT")
    val OTHER = Value("OTHER")
  }

  def string_from_tokens(tokens: List[Token], starts: Token => Int): String = {
    def stop(t: Token) = starts(t) + t.length
    tokens match {
      case Nil => ""
      case tok :: toks =>
        val (res, _) = toks.foldLeft(tok.content, stop(tok))((a, token) =>
          (a._1 + " " * (starts(token) - a._2) + token.content, stop(token)))
        res
    }
  }

}

class Token(
  val content: String,
  val kind: Token.Kind.Value)
{
  override def toString = content
  val length = content.length
  val is_start = kind == Token.Kind.COMMAND_START || kind == Token.Kind.COMMENT
}
