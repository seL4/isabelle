/*  Title:      Pure/System/isabelle_syntax.scala
    Author:     Makarius

Isabelle outer syntax.
*/

package isabelle


object Isabelle_Syntax
{
  /* string token */

  def append_string(str: String, result: StringBuilder)
  {
    result.append("\"")
    for (c <- str) {
      if (c < 32 || c == '\\' || c == '\"') {
        result.append("\\")
        if (c < 10) result.append('0')
        if (c < 100) result.append('0')
        result.append(c.asInstanceOf[Int].toString)
      }
      else result.append(c)
    }
    result.append("\"")
  }

  def encode_string(str: String) =
  {
    val result = new StringBuilder(str.length + 10)
    append_string(str, result)
    result.toString
  }


  /* list */

  def append_list[A](append_elem: (A, StringBuilder) => Unit, body: Iterable[A],
    result: StringBuilder)
  {
    result.append("(")
    val elems = body.elements
    if (elems.hasNext) append_elem(elems.next, result)
    while (elems.hasNext) {
      result.append(", ")
      append_elem(elems.next, result)
    }
    result.append(")")
  }

  def encode_list[A](append_elem: (A, StringBuilder) => Unit, elems: Iterable[A]) =
  {
    val result = new StringBuilder
    append_list(append_elem, elems, result)
    result.toString
  }


  /* properties */

  def append_properties(props: List[(String, String)], result: StringBuilder)
  {
    append_list((p: (String, String), res) =>
      { append_string(p._1, res); res.append(" = "); append_string(p._2, res) }, props, result)
  }

  def encode_properties(props: List[(String, String)]) =
  {
    val result = new StringBuilder
    append_properties(props, result)
    result.toString
  }
}
