/*  Title:      Pure/General/yxml.scala
    Author:     Makarius

Efficient text representation of XML trees.
*/

package isabelle


object YXML
{
  /* chunk markers */

  private val X = '\5'
  private val Y = '\6'
  private val X_string = X.toString
  private val Y_string = Y.toString


  /* iterate over chunks (resembles space_explode in ML) */

  private def chunks(sep: Char, source: CharSequence) = new Iterator[CharSequence]
  {
    private val end = source.length
    private var state = if (end == 0) None else get_chunk(-1)
    private def get_chunk(i: Int) =
    {
      if (i < end) {
        var j = i; do j += 1 while (j < end && source.charAt(j) != sep)
        Some((source.subSequence(i + 1, j), j))
      }
      else None
    }

    def hasNext() = state.isDefined
    def next() = state match {
      case Some((s, i)) => { state = get_chunk(i); s }
      case None => throw new NoSuchElementException("next on empty iterator")
    }
  }


  /* decoding pseudo UTF-8 */

  private class Decode_Chars(decode: String => String,
    buffer: Array[Byte], start: Int, end: Int) extends CharSequence
  {
    def length: Int = end - start
    def charAt(i: Int): Char = (buffer(start + i).asInstanceOf[Int] & 0xFF).asInstanceOf[Char]
    def subSequence(i: Int, j: Int): CharSequence =
      new Decode_Chars(decode, buffer, start + i, start + j)

    // toString with adhoc decoding: abuse of CharSequence interface
    override def toString: String = decode(Standard_System.decode_permissive_utf8(this))
  }

  def decode_chars(decode: String => String,
    buffer: Array[Byte], start: Int, end: Int): CharSequence =
  {
    require(0 <= start && start <= end && end <= buffer.length)
    new Decode_Chars(decode, buffer, start, end)
  }


  /* parsing */

  private def err(msg: String) = error("Malformed YXML: " + msg)
  private def err_attribute() = err("bad attribute")
  private def err_element() = err("bad element")
  private def err_unbalanced(name: String) =
    if (name == "") err("unbalanced element")
    else err("unbalanced element \"" + name + "\"")

  private def parse_attrib(source: CharSequence) = {
    val s = source.toString
    val i = s.indexOf('=')
    if (i <= 0) err_attribute()
    (s.substring(0, i).intern, s.substring(i + 1))
  }


  def parse_body(source: CharSequence): List[XML.Tree] =
  {
    /* stack operations */

    var stack: List[((String, XML.Attributes), List[XML.Tree])] = null

    def add(x: XML.Tree) = (stack: @unchecked) match {
      case ((elem, body) :: pending) => stack = (elem, x :: body) :: pending
    }

    def push(name: String, atts: XML.Attributes) =
      if (name == "") err_element()
      else stack = ((name, atts), Nil) :: stack

    def pop() = (stack: @unchecked) match {
      case ((("", _), _) :: _) => err_unbalanced("")
      case (((name, atts), body) :: pending) =>
        stack = pending; add(XML.Elem(name, atts, body.reverse))
    }


    /* parse chunks */

    stack = List((("", Nil), Nil))
    for (chunk <- chunks(X, source) if chunk.length != 0) {
      if (chunk.length == 1 && chunk.charAt(0) == Y) pop()
      else {
        chunks(Y, chunk).toList match {
          case ch :: name :: atts if ch.length == 0 =>
            push(name.toString.intern, atts.map(parse_attrib))
          case txts => for (txt <- txts) add(XML.Text(txt.toString))
        }
      }
    }
    stack match {
      case List((("", _), result)) => result.reverse
      case ((name, _), _) :: _ => err_unbalanced(name)
    }
  }

  def parse(source: CharSequence): XML.Tree =
    parse_body(source) match {
      case List(result) => result
      case Nil => XML.Text("")
      case _ => err("multiple results")
    }


  /* failsafe parsing */

  private def markup_failsafe(source: CharSequence) =
    XML.Elem (Markup.MALFORMED, Nil,
      List(XML.Text(source.toString.replace(X_string, "\\<^X>").replace(Y_string, "\\<^Y>"))))

  def parse_body_failsafe(source: CharSequence): List[XML.Tree] =
  {
    try { parse_body(source) }
    catch { case _: RuntimeException => List(markup_failsafe(source)) }
  }

  def parse_failsafe(source: CharSequence): XML.Tree =
  {
    try { parse(source) }
    catch { case _: RuntimeException => markup_failsafe(source) }
  }
}
