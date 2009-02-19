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

  def check_start(t: Token, P: Int => Boolean) = t != null && P(t.start)
  def check_stop(t: Token, P: Int => Boolean) = t != null && P(t.stop)

  private def fill(n: Int) = {
    val blanks = new Array[Char](n)
    for(i <- 0 to n - 1) blanks(i) = ' '
    new String(blanks)
  }
  def string_from_tokens (tokens: List[Token]): String = {
    tokens match {
      case Nil => ""
      case t::tokens => (tokens.foldLeft
          (t.content, t.stop)
          ((a, token) => (a._1 + fill(token.start - a._2) + token.content, token.stop))
        )._1
    }
  }

}

class Token(var start: Int, val content: String, val kind: Token.Kind.Value) {
  val length = content.length
  def stop = start + length
  override def toString = content + "(" + kind + ")"
}
