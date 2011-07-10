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
    type T[A] = A => XML.Body


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

    val properties: T[List[(String, String)]] =
      (props => List(XML.Elem(Markup(":", props), Nil)))

    val string: T[String] = (s => if (s.isEmpty) Nil else List(XML.Text(s)))

    val long: T[Long] = (x => string(long_atom(x)))

    val int: T[Int] = (x => string(int_atom(x)))

    val bool: T[Boolean] = (x => string(bool_atom(x)))

    val unit: T[Unit] = (x => string(unit_atom(x)))

    def pair[A, B](f: T[A], g: T[B]): T[(A, B)] =
      (x => List(node(f(x._1)), node(g(x._2))))

    def triple[A, B, C](f: T[A], g: T[B], h: T[C]): T[(A, B, C)] =
      (x => List(node(f(x._1)), node(g(x._2)), node(h(x._3))))

    def list[A](f: T[A]): T[List[A]] =
      (xs => xs.map((x: A) => node(f(x))))

    def option[A](f: T[A]): T[Option[A]] =
    {
      case None => Nil
      case Some(x) => List(node(f(x)))
    }

    def variant[A](fs: List[PartialFunction[A, XML.Body]]): T[A] =
    {
      case x =>
        val (f, tag) = fs.iterator.zipWithIndex.find(p => p._1.isDefinedAt(x)).get
        List(tagged(tag, f(x)))
    }
  }



  /** dest **/

  class XML_Atom(s: String) extends Exception(s)
  class XML_Body(body: XML.Body) extends Exception

  object Dest
  {
    type T[A] = XML.Body => A


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

    val properties: T[List[(String, String)]] =
    {
      case List(XML.Elem(Markup(":", props), Nil)) => props
      case ts => throw new XML_Body(ts)
    }

    val string: T[String] =
    {
      case Nil => ""
      case List(XML.Text(s)) => s
      case ts => throw new XML_Body(ts)
    }

    val long: T[Long] = (x => long_atom(string(x)))

    val int: T[Int] = (x => int_atom(string(x)))

    val bool: T[Boolean] = (x => bool_atom(string(x)))

    val unit: T[Unit] = (x => unit_atom(string(x)))

    def pair[A, B](f: T[A], g: T[B]): T[(A, B)] =
    {
      case List(t1, t2) => (f(node(t1)), g(node(t2)))
      case ts => throw new XML_Body(ts)
    }

    def triple[A, B, C](f: T[A], g: T[B], h: T[C]): T[(A, B, C)] =
    {
      case List(t1, t2, t3) => (f(node(t1)), g(node(t2)), h(node(t3)))
      case ts => throw new XML_Body(ts)
    }

    def list[A](f: T[A]): T[List[A]] =
      (ts => ts.map(t => f(node(t))))

    def option[A](f: T[A]): T[Option[A]] =
    {
      case Nil => None
      case List(t) => Some(f(node(t)))
      case ts => throw new XML_Body(ts)
    }

    def variant[A](fs: List[T[A]]): T[A] =
    {
      case List(t) =>
        val (tag, ts) = tagged(t)
        fs(tag)(ts)
      case ts => throw new XML_Body(ts)
    }
  }
}
