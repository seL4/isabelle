/*  Title:      Pure/General/properties.scala
    Author:     Makarius

Property lists.
*/

package isabelle


object Properties {
  /* entries */

  type Entry = (java.lang.String, java.lang.String)
  type T = List[Entry]

  object Eq {
    def apply(a: java.lang.String, b: java.lang.String): java.lang.String = a + "=" + b
    def apply(entry: Entry): java.lang.String = apply(entry._1, entry._2)

    def unapply(str: java.lang.String): Option[Entry] = {
      val i = str.indexOf('=')
      if (i <= 0) None else Some((str.slice(0, i), str.drop(i + 1)))
    }

    def parse(s: java.lang.String): Entry =
      unapply(s) getOrElse error("Bad property entry: " + quote(s))
  }

  def defined(props: T, name: java.lang.String): scala.Boolean =
    props.exists({ case (x, _) => x == name })

  def get(props: T, name: java.lang.String): Option[java.lang.String] =
    props.collectFirst({ case (x, y) if x == name => y })

  def put(props: T, entry: Entry): T = {
    val (x, y) = entry
    def update(ps: T): T =
      ps match {
        case (p @ (x1, _)) :: rest =>
          if (x1 == x) (x1, y) :: rest else p :: update(rest)
        case Nil => Nil
      }
    if (defined(props, x)) update(props) else entry :: props
  }


  /* external storage */

  def encode(ps: T): Bytes = {
    if (ps.isEmpty) Bytes.empty
    else YXML.bytes_of_body(XML.Encode.properties(ps))
  }

  def decode(bs: Bytes, cache: XML.Cache = XML.Cache.none): T = {
    if (bs.is_empty) Nil
    else cache.props(XML.Decode.properties(YXML.parse_body(bs)))
  }

  def compress(ps: List[T],
    options: Compress.Options = Compress.Options(),
    cache: Compress.Cache = Compress.Cache.none
  ): Bytes = {
    if (ps.isEmpty) Bytes.empty
    else {
      YXML.bytes_of_body(XML.Encode.list(XML.Encode.properties)(ps)).
        compress(options = options, cache = cache)
    }
  }

  def uncompress(bs: Bytes, cache: XML.Cache = XML.Cache.none): List[T] = {
    if (bs.is_empty) Nil
    else {
      val ps =
        XML.Decode.list(XML.Decode.properties)(
          YXML.parse_body(bs.uncompress(cache = cache.compress)))
      if (cache.no_cache) ps else ps.map(cache.props)
    }
  }


  /* multi-line entries */

  def encode_lines(props: T): T = props.map({ case (a, b) => (a, Library.encode_lines(b)) })
  def decode_lines(props: T): T = props.map({ case (a, b) => (a, Library.decode_lines(b)) })

  def lines_nonempty(x: java.lang.String, ys: List[java.lang.String]): Properties.T =
    if (ys.isEmpty) Nil else List((x, cat_lines(ys)))


  /* typed view on entries (read-only) */

  trait View {
    // key
    def name: java.lang.String
    override def toString: java.lang.String = name
    override def equals(that: Any): scala.Boolean =
      that match {
        case other: View => name == other.name
        case _ => false
      }
    override def hashCode: scala.Int = name.hashCode

    // value
    type V
    def default: V
    def unapply(props: T): Option[V]
    def get(props: T): V = unapply(props).getOrElse(default)
  }

  class String_View(override val name: java.lang.String) extends View {
    type V = java.lang.String
    override def default: V = ""
    override def unapply(props: T): Option[V] =
      Properties.get(props, name)
  }

  class Boolean_View(override val name: java.lang.String) extends View {
    type V = scala.Boolean
    override def default: V = false
    override def unapply(props: T): Option[V] =
      Properties.get(props, name).flatMap(Value.Boolean.unapply)
  }

  class Int_View(override val name: java.lang.String) extends View {
    type V = scala.Int
    override def default: V = 0
    override def unapply(props: T): Option[V] =
      Properties.get(props, name).flatMap(Value.Int.unapply)
  }

  class Long_View(override val name: java.lang.String) extends View {
    type V = scala.Long
    override def default: V = 0L
    override def unapply(props: T): Option[V] =
      Properties.get(props, name).flatMap(Value.Long.unapply)
  }

  class Double_View(override val name: java.lang.String) extends View {
    type V = scala.Double
    override def default: V = 0.0
    override def unapply(props: T): Option[V] =
      Properties.get(props, name).flatMap(Value.Double.unapply)
  }


  /* typed access to entries */

  trait Access extends View {
    def apply_value(value: V): java.lang.String
    def apply(value: V): T = List(name -> apply_value(value))
    def make(value: V): T = if (value == default) Nil else apply(value)
  }

  class String(name: java.lang.String) extends String_View(name) with Access {
    override def apply_value(value: V): java.lang.String = value
  }

  class Boolean(name: java.lang.String) extends Boolean_View(name) with Access {
    override def apply_value(value: V): java.lang.String = Value.Boolean(value)
  }

  class Int(name: java.lang.String) extends Int_View(name) with Access {
    override def apply_value(value: V): java.lang.String = Value.Int(value)
  }

  class Long(name: java.lang.String) extends Long_View(name) with Access {
    override def apply_value(value: V): java.lang.String = Value.Long(value)
  }

  class Double(name: java.lang.String) extends Double_View(name) with Access {
    override def apply_value(value: V): java.lang.String = Value.Double(value)
  }
}
