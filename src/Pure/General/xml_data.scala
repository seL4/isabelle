/*  Title:      Pure/General/xml_data.scala
    Author:     Makarius

XML as basic data representation language.
*/

package isabelle



object XML_Data
{
  /* basic values */

  class XML_Atom(s: String) extends Exception(s)


  private def make_long_atom(i: Long): String = i.toString

  private def dest_long_atom(s: String): Long =
    try { java.lang.Long.parseLong(s) }
    catch { case e: NumberFormatException => throw new XML_Atom(s) }


  private def make_int_atom(i: Int): String = i.toString

  private def dest_int_atom(s: String): Int =
    try { Integer.parseInt(s) }
    catch { case e: NumberFormatException => throw new XML_Atom(s) }


  private def make_bool_atom(b: Boolean): String = if (b) "1" else "0"

  private def dest_bool_atom(s: String): Boolean =
    if (s == "1") true
    else if (s == "0") false
    else throw new XML_Atom(s)


  private def make_unit_atom(u: Unit) = ""

  private def dest_unit_atom(s: String): Unit =
    if (s == "") () else throw new XML_Atom(s)


  /* structural nodes */

  class XML_Body(body: XML.Body) extends Exception

  private def make_node(ts: XML.Body): XML.Tree = XML.Elem(Markup(":", Nil), ts)

  private def dest_node(t: XML.Tree): XML.Body =
    t match {
      case XML.Elem(Markup(":", Nil), ts) => ts
      case _ => throw new XML_Body(List(t))
    }


  /* representation of standard types */

  def make_properties(props: List[(String, String)]): XML.Body =
    List(XML.Elem(Markup(":", props), Nil))

  def dest_properties(ts: XML.Body): List[(String, String)] =
    ts match {
      case List(XML.Elem(Markup(":", props), Nil)) => props
      case _ => throw new XML_Body(ts)
    }


  def make_string(s: String): XML.Body = if (s.isEmpty) Nil else List(XML.Text(s))

  def dest_string(ts: XML.Body): String =
    ts match {
      case Nil => ""
      case List(XML.Text(s)) => s
      case _ => throw new XML_Body(ts)
    }


  def make_long(i: Long): XML.Body = make_string(make_long_atom(i))
  def dest_long(ts: XML.Body): Long = dest_long_atom(dest_string(ts))

  def make_int(i: Int): XML.Body = make_string(make_int_atom(i))
  def dest_int(ts: XML.Body): Int = dest_int_atom(dest_string(ts))

  def make_bool(b: Boolean): XML.Body = make_string(make_bool_atom(b))
  def dest_bool(ts: XML.Body) = dest_bool_atom(dest_string(ts))

  def make_unit(u: Unit): XML.Body = make_string(make_unit_atom(u))
  def dest_unit(ts: XML.Body): Unit = dest_unit_atom(dest_string(ts))


  def make_pair[A, B](make1: A => XML.Body)(make2: B => XML.Body)(p: (A, B)): XML.Body =
    List(make_node(make1(p._1)), make_node(make2(p._2)))

  def dest_pair[A, B](dest1: XML.Body => A)(dest2: XML.Body => B)(ts: XML.Body): (A, B) =
    ts match {
      case List(t1, t2) => (dest1(dest_node(t1)), dest2(dest_node(t2)))
      case _ => throw new XML_Body(ts)
    }


  def make_triple[A, B, C](make1: A => XML.Body)(make2: B => XML.Body)(make3: C => XML.Body)
      (p: (A, B, C)): XML.Body =
    List(make_node(make1(p._1)), make_node(make2(p._2)), make_node(make3(p._3)))

  def dest_triple[A, B, C](dest1: XML.Body => A)(dest2: XML.Body => B)(dest3: XML.Body => C)
      (ts: XML.Body): (A, B, C) =
    ts match {
      case List(t1, t2, t3) => (dest1(dest_node(t1)), dest2(dest_node(t2)), dest3(dest_node(t3)))
      case _ => throw new XML_Body(ts)
    }


  def make_list[A](make: A => XML.Body)(xs: List[A]): XML.Body =
    xs.map((x: A) => make_node(make(x)))

  def dest_list[A](dest: XML.Body => A)(ts: XML.Body): List[A] =
    ts.map((t: XML.Tree) => dest(dest_node(t)))


  def make_option[A](make: A => XML.Body)(opt: Option[A]): XML.Body =
    opt match {
      case None => make_list(make)(Nil)
      case Some(x) => make_list(make)(List(x))
    }

  def dest_option[A](dest: XML.Body => A)(ts: XML.Body): Option[A] =
    dest_list(dest)(ts) match {
      case Nil => None
      case List(x) => Some(x)
      case _ => throw new XML_Body(ts)
    }
}
