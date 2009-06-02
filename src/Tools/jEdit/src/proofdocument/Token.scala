/*
 * Document tokens as text ranges
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.proofdocument


import isabelle.prover.Command


object Token {
  object Kind extends Enumeration {
    val COMMAND_START = Value("COMMAND_START")
    val COMMENT = Value("COMMENT")
    val OTHER = Value("OTHER")
  }

  def string_from_tokens (tokens: List[Token], starts: Map[Token, Int]): String = {
    def stop(t: Token) = starts(t) + t.length
    tokens match {
      case Nil => ""
      case t::tokens => ( tokens.foldLeft
          (t.content, stop(t))
          ((a, token) => (a._1 + " " * (starts(token) - a._2) + token.content, stop(token)))
        )._1
    }
  }

}

class Token(val content: String, val kind: Token.Kind.Value) {
  val length = content.length
  override def toString = content
}
