/*  Title:      Pure/General/properties.scala
    Author:     Makarius

Property lists.
*/

package isabelle


object Properties
{
  /* entries */

  type Entry = (java.lang.String, java.lang.String)
  type T = List[Entry]

  def defined(props: T, name: java.lang.String): java.lang.Boolean =
    props.exists({ case (x, _) => x == name })

  def get(props: T, name: java.lang.String): Option[java.lang.String] =
    props.collectFirst({ case (x, y) if x == name => y })

  def put(props: T, entry: Entry): T =
  {
    val (x, y) = entry
    def update(ps: T): T =
      ps match {
        case (p @ (x1, _)) :: rest =>
          if (x1 == x) (x1, y) :: rest else p :: update(rest)
        case Nil => Nil
      }
    if (defined(props, x)) update(props) else entry :: props
  }


  /* multi-line entries */

  val separator = '\u000b'

  def encode_lines(s: java.lang.String): java.lang.String = s.replace('\n', separator)
  def decode_lines(s: java.lang.String): java.lang.String = s.replace(separator, '\n')

  def encode_lines(props: T): T = props.map({ case (a, b) => (a, encode_lines(b)) })
  def decode_lines(props: T): T = props.map({ case (a, b) => (a, decode_lines(b)) })

  def lines_nonempty(x: java.lang.String, ys: List[java.lang.String]): Properties.T =
    if (ys.isEmpty) Nil else List((x, cat_lines(ys)))


  /* entry types */

  class String(val name: java.lang.String)
  {
    def apply(value: java.lang.String): T = List((name, value))
    def unapply(props: T): Option[java.lang.String] =
      props.find(_._1 == name).map(_._2)
  }

  class Boolean(val name: java.lang.String)
  {
    def apply(value: scala.Boolean): T = List((name, Value.Boolean(value)))
    def unapply(props: T): Option[scala.Boolean] =
      props.find(_._1 == name) match {
        case None => None
        case Some((_, value)) => Value.Boolean.unapply(value)
      }
  }

  class Int(val name: java.lang.String)
  {
    def apply(value: scala.Int): T = List((name, Value.Int(value)))
    def unapply(props: T): Option[scala.Int] =
      props.find(_._1 == name) match {
        case None => None
        case Some((_, value)) => Value.Int.unapply(value)
      }
  }

  class Long(val name: java.lang.String)
  {
    def apply(value: scala.Long): T = List((name, Value.Long(value)))
    def unapply(props: T): Option[scala.Long] =
      props.find(_._1 == name) match {
        case None => None
        case Some((_, value)) => Value.Long.unapply(value)
      }
  }

  class Double(val name: java.lang.String)
  {
    def apply(value: scala.Double): T = List((name, Value.Double(value)))
    def unapply(props: T): Option[scala.Double] =
      props.find(_._1 == name) match {
        case None => None
        case Some((_, value)) => Value.Double.unapply(value)
      }
  }


  /* cached store */

  trait Store
  {
    val xml_cache: XML.Cache = new XML.Cache()

    def encode_properties(ps: T): Bytes =
      Bytes(YXML.string_of_body(XML.Encode.properties(ps)))

    def decode_properties(bs: Bytes): T =
      xml_cache.props(XML.Decode.properties(YXML.parse_body(bs.text)))

    def compress_properties(ps: List[T], options: XZ.Options = XZ.options()): Bytes =
    {
      if (ps.isEmpty) Bytes.empty
      else Bytes(YXML.string_of_body(XML.Encode.list(XML.Encode.properties)(ps))).compress(options)
    }

    def uncompress_properties(bs: Bytes): List[T] =
    {
      if (bs.isEmpty) Nil
      else
        XML.Decode.list(XML.Decode.properties)(YXML.parse_body(bs.uncompress().text)).
          map(xml_cache.props(_))
    }
  }
}
