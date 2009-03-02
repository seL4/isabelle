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

  def check_start(t: Token, P: Int => Boolean) = { t != null && P(t.start) }
  def check_stop(t: Token, P: Int => Boolean) = { t != null && P(t.stop) }

  def scan(s: Token, f: Token => Boolean): Token =
  {
    var current = s
    while (current != null) {
      val next = current.next
      if (next == null || f(next)) return current
      current = next
    }
    return null
  }
}

class Token(var start: Int, var stop: Int, val kind: Token.Kind.Value)
{
  var next: Token = null
  var prev: Token = null
  var command: Command = null
  
  def length = stop - start

  def shift(offset: Int, bottom_clamp: Int) {
    start = bottom_clamp max (start + offset)
    stop = bottom_clamp max (stop + offset)
  }

  override def toString: String = "[" + start + ":" + stop + "]"
  override def hashCode: Int = (31 + start) * 31 + stop

  override def equals(obj: Any): Boolean =
  {
    if (super.equals(obj)) return true
    if (null == obj) return false
    obj match {
      case other: Token => (start == other.start) && (stop == other.stop)
      case other: Any => false
    }
  }
}
