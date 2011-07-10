/*  Title:      Pure/General/xml_data.scala
    Author:     Makarius

XML as basic data representation language.
*/

package isabelle



object XML_Data
{
  /** make **/

  object Make
  {
    /* basic values */

    private def long_atom(i: Long): String = i.toString

    private def int_atom(i: Int): String = i.toString

    private def bool_atom(b: Boolean): String = if (b) "1" else "0"

    private def unit_atom(u: Unit) = ""


    /* structural nodes */

    private def node(ts: XML.Body): XML.Tree = XML.Elem(Markup(":", Nil), ts)

    private def tagged(tag: Int, ts: XML.Body): XML.Tree =
      XML.Elem(Markup(int_atom(tag), Nil), ts)


    /* representation of standard types */

    def properties(props: List[(String, String)]): XML.Body =
      List(XML.Elem(Markup(":", props), Nil))

    def string(s: String): XML.Body = if (s.isEmpty) Nil else List(XML.Text(s))

    def long(i: Long): XML.Body = string(long_atom(i))

    def int(i: Int): XML.Body = string(int_atom(i))

    def bool(b: Boolean): XML.Body = string(bool_atom(b))

    def unit(u: Unit): XML.Body = string(unit_atom(u))

    def pair[A, B](f: A => XML.Body, g: B => XML.Body)(p: (A, B)): XML.Body =
      List(node(f(p._1)), node(g(p._2)))

    def triple[A, B, C](f: A => XML.Body, g: B => XML.Body, h: C => XML.Body)
        (p: (A, B, C)): XML.Body =
      List(node(f(p._1)), node(g(p._2)), node(h(p._3)))

    def list[A](f: A => XML.Body)(xs: List[A]): XML.Body =
      xs.map((x: A) => node(f(x)))

    def option[A](f: A => XML.Body)(opt: Option[A]): XML.Body =
      opt match {
        case None => Nil
        case Some(x) => List(node(f(x)))
      }

    def variant[A](fs: List[PartialFunction[A, XML.Body]])(x: A): XML.Body =
    {
      val (f, tag) = fs.iterator.zipWithIndex.find(p => p._1.isDefinedAt(x)).get
      List(tagged(tag, f(x)))
    }
  }



  /** dest **/

  class XML_Atom(s: String) extends Exception(s)
  class XML_Body(body: XML.Body) extends Exception

  object Dest
  {
     /* basic values */

    private def long_atom(s: String): Long =
      try { java.lang.Long.parseLong(s) }
      catch { case e: NumberFormatException => throw new XML_Atom(s) }

    private def int_atom(s: String): Int =
      try { Integer.parseInt(s) }
      catch { case e: NumberFormatException => throw new XML_Atom(s) }

    private def bool_atom(s: String): Boolean =
      if (s == "1") true
      else if (s == "0") false
      else throw new XML_Atom(s)

    private def unit_atom(s: String): Unit =
      if (s == "") () else throw new XML_Atom(s)


    /* structural nodes */

    private def node(t: XML.Tree): XML.Body =
      t match {
        case XML.Elem(Markup(":", Nil), ts) => ts
        case _ => throw new XML_Body(List(t))
      }

    private def tagged(t: XML.Tree): (Int, XML.Body) =
      t match {
        case XML.Elem(Markup(s, Nil), ts) => (int_atom(s), ts)
        case _ => throw new XML_Body(List(t))
      }


    /* representation of standard types */

    def properties(ts: XML.Body): List[(String, String)] =
      ts match {
        case List(XML.Elem(Markup(":", props), Nil)) => props
        case _ => throw new XML_Body(ts)
      }

    def string(ts: XML.Body): String =
      ts match {
        case Nil => ""
        case List(XML.Text(s)) => s
        case _ => throw new XML_Body(ts)
      }

    def long(ts: XML.Body): Long = long_atom(string(ts))

    def int(ts: XML.Body): Int = int_atom(string(ts))

    def bool(ts: XML.Body) = bool_atom(string(ts))

    def unit(ts: XML.Body): Unit = unit_atom(string(ts))

    def pair[A, B](f: XML.Body => A, g: XML.Body => B)(ts: XML.Body): (A, B) =
      ts match {
        case List(t1, t2) => (f(node(t1)), g(node(t2)))
        case _ => throw new XML_Body(ts)
      }

    def triple[A, B, C](f: XML.Body => A, g: XML.Body => B, h: XML.Body => C)
        (ts: XML.Body): (A, B, C) =
      ts match {
        case List(t1, t2, t3) => (f(node(t1)), g(node(t2)), h(node(t3)))
        case _ => throw new XML_Body(ts)
      }

    def list[A](f: XML.Body => A)(ts: XML.Body): List[A] =
      ts.map((t: XML.Tree) => f(node(t)))

    def option[A](f: XML.Body => A)(ts: XML.Body): Option[A] =
      ts match {
        case Nil => None
        case List(t) => Some(f(node(t)))
        case _ => throw new XML_Body(ts)
      }

    def variant[A](fs: List[XML.Body => A])(ts: XML.Body): A =
      ts match {
        case List(t) =>
          val (tag, ts) = tagged(t)
          fs(tag)(ts)
        case _ => throw new XML_Body(ts)
      }
  }
}
