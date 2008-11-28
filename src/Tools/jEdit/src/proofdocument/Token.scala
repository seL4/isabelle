package isabelle.proofdocument

object Token {
  object Kind {
    val COMMAND_START = "COMMAND_START"
    val COMMENT = "COMMENT"
  }

  def checkStart(t : Token[_], P : (Int) => Boolean)
    = t != null && P(t.start)

  def checkStop(t : Token[_], P : (Int) => Boolean)
    = t != null && P(t.stop)

  def scan(s : Token[_], f : (Token[_]) => Boolean) : Token[_] = {
    var current = s
    while (current != null) {
      val next = current.next
      if (next == null || f(next))
        return current
      current = next
    }
    return null
  }

}

class Token[C](var start : Int, var stop : Int, var kind : String) {
  var next : Token[C] = null
  var previous : Token[C] = null
  var command : C = null.asInstanceOf[C]
  
  def length = stop - start

  def shift(offset : Int, bottomClamp : Int) {
    start = bottomClamp max (start + offset)
    stop = bottomClamp max (stop + offset)
  }
  
  override def hashCode() : Int = (31 + start) * 31 + stop

  override def equals(obj : Any) : Boolean = {
    if (super.equals(obj))
      return true;
    
    if (null == obj)
      return false;
    
    obj match {
      case other: Token[_] => 
        (start == other.start) && (stop == other.stop)
      case other: Any => false  
    }
  }
}
