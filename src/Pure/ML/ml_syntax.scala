/*  Title:      Pure/ML/ml_syntax.scala
    Author:     Makarius

Concrete ML syntax for basic values.
*/

package isabelle


object ML_Syntax {
  type Source = String


  /* numbers */

  private def signed(s: String): Source =
    if (s(0) == '-') "~" + s.substring(1).nn else s

  def print_int(x: Int): Source = signed(Value.Int(x))
  def print_long(x: Long): Source = signed(Value.Long(x))
  def print_double(x: Double): Source = signed(x.toString)


  /* string */

  private def print_byte(c: Byte): Source =
    c match {
      case 34 => "\\\""
      case 92 => "\\\\"
      case 9 => "\\t"
      case 10 => "\\n"
      case 12 => "\\f"
      case 13 => "\\r"
      case _ =>
        if (c < 0) "\\" + Value.Int(256 + c)
        else if (c < 32) new String(Array[Char](92, 94, (c + 64).toChar))
        else if (c < 127) Symbol.ascii(c.toChar)
        else "\\" + Value.Int(c)
    }

  private def print_symbol(s: Symbol.Symbol): Source =
    if (s.startsWith("\\<")) s
    else UTF8.bytes(s).iterator.map(print_byte).mkString

  def print_string_bytes(str: String): Source =
    quote(UTF8.bytes(str).iterator.map(print_byte).mkString)

  def print_string_symbols(str: String): Source =
    quote(Symbol.iterator(str).map(print_symbol).mkString)


  /* pair */

  def print_pair[A, B](f: A => Source, g: B => Source)(pair: (A, B)): Source =
    "(" + f(pair._1) + ", " + g(pair._2) + ")"


  /* list */

  def print_list[A](f: A => Source)(list: List[A]): Source =
    "[" + commas(list.map(f)) + "]"


  /* properties */

  def print_properties(props: Properties.T): Source =
    print_list(print_pair(print_string_bytes, print_string_bytes))(props)
}
