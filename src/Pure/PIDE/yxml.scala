/*  Title:      Pure/PIDE/yxml.scala
    Author:     Makarius

Efficient text representation of XML trees.  Suitable for direct
inlining into plain text.
*/

package isabelle


import scala.collection.mutable


object YXML {
  /* chunk markers */

  val X_byte: Byte = 5
  val Y_byte: Byte = 6

  val X = X_byte.toChar
  val Y = Y_byte.toChar

  val is_X: Char => Boolean = _ == X
  val is_Y: Char => Boolean = _ == Y

  val X_string: String = X.toString
  val Y_string: String = Y.toString
  val XY_string: String = X_string + Y_string
  val XYX_string: String = XY_string + X_string

  def detect(s: String): Boolean = s.exists(c => c == X || c == Y)
  def detect_elem(s: String): Boolean = s.startsWith(XY_string)


  /* string representation */

  trait Output extends XML.Traversal {
    def byte(b: Byte): Unit
    def string(s: String): Unit

    // XML.Traversal
    override def text(s: String): Unit = string(s)
    override def elem(markup: Markup, end: Boolean = false): Unit = {
      byte(X_byte)
      byte(Y_byte)
      string(markup.name)
      for ((a, b) <- markup.properties) {
        byte(Y_byte)
        string(a)
        byte('='.toByte)
        string(b)
      }
      byte(X_byte)
      if (end) end_elem(markup.name)
    }
    override def end_elem(name: String): Unit = {
      byte(X_byte)
      byte(Y_byte)
      byte(X_byte)
    }
  }

  class Output_String(builder: StringBuilder, recode: String => String = identity) extends Output {
    override def byte(b: Byte): Unit = { builder += b.toChar }
    override def string(s: String): Unit = { builder ++= recode(s) }
    def result(ts: List[XML.Tree]): String = { traverse(ts); builder.toString }
  }

  class Output_Bytes(builder: Bytes.Builder, recode: String => String = identity) extends Output {
    override def byte(b: Byte): Unit = { builder += b }
    override def string(s: String): Unit = { builder += recode(s) }
  }

  def string_of_body(body: XML.Body, recode: String => String = identity): String =
    new Output_String(new StringBuilder, recode = recode).result(body)

  def string_of_tree(tree: XML.Tree, recode: String => String = identity): String =
    string_of_body(List(tree), recode = recode)

  def bytes_of_body(body: XML.Body, recode: String => String = identity): Bytes =
    Bytes.Builder.use()(builder => new Output_Bytes(builder, recode = recode).traverse(body))

  def bytes_of_tree(tree: XML.Tree, recode: String => String = identity): Bytes =
    bytes_of_body(List(tree), recode = recode)


  /* parsing */

  private def err(msg: String) = error("Malformed YXML: " + msg)
  private def err_attribute() = err("bad attribute")
  private def err_element() = err("bad element")
  private def err_unbalanced(name: String) =
    if (name == "") err("unbalanced element")
    else err("unbalanced element " + quote(name))

  object Source {
    def apply(s: String): Source = new Source_String(s)
  }

  trait Source {
    def is_empty: Boolean
    def is_X: Boolean
    def is_Y: Boolean
    def iterator_X: Iterator[Source]
    def iterator_Y: Iterator[Source]
    def text: String
  }

  class Source_String(source: String) extends Source {
    override def is_empty: Boolean = source.isEmpty
    override def is_X: Boolean = source.length == 1 && source(0) == X
    override def is_Y: Boolean = source.length == 1 && source(0) == Y
    override def iterator_X: Iterator[Source] =
      Library.separated_chunks(X, source).map(Source.apply)
    override def iterator_Y: Iterator[Source] =
      Library.separated_chunks(Y, source).map(Source.apply)
    override def text: String = source
  }

  def parse_body(
    source: Source,
    recode: String => String = identity,
    cache: XML.Cache = XML.Cache.none
  ): XML.Body = {
    /* parse + recode */

    def parse_string(s: Source): String = recode(s.text)

    def parse_attrib(s: Source): (String, String) =
      Properties.Eq.unapply(parse_string(s)) getOrElse err_attribute()


    /* stack operations */

    def buffer(): mutable.ListBuffer[XML.Tree] = new mutable.ListBuffer[XML.Tree]
    var stack: List[(Markup, mutable.ListBuffer[XML.Tree])] = List((Markup.Empty, buffer()))

    def add(x: XML.Tree): Unit =
      (stack: @unchecked) match { case (_, body) :: _ => body += x }

    def push(name: String, atts: XML.Attributes): Unit =
      if (name == "") err_element()
      else stack = (cache.markup(Markup(name, atts)), buffer()) :: stack

    def pop(): Unit =
      (stack: @unchecked) match {
        case (Markup.Empty, _) :: _ => err_unbalanced("")
        case (markup, body) :: pending =>
          stack = pending
          add(cache.tree0(XML.Elem(markup, body.toList)))
      }


    /* parse chunks */

    for (chunk <- source.iterator_X if !chunk.is_empty) {
      if (chunk.is_Y) pop()
      else {
        chunk.iterator_Y.toList match {
          case ch :: name :: atts if ch.is_empty =>
            push(parse_string(name), atts.map(parse_attrib))
          case txts =>
            for (txt <- txts) add(cache.tree0(XML.Text(cache.string(parse_string(txt)))))
        }
      }
    }
    (stack: @unchecked) match {
      case List((Markup.Empty, body)) => body.toList
      case (Markup(name, _), _) :: _ => err_unbalanced(name)
    }
  }

  def parse(
    source: Source,
    recode: String => String = identity,
    cache: XML.Cache = XML.Cache.none
  ): XML.Tree =
    parse_body(source, recode = recode, cache = cache) match {
      case List(result) => result
      case Nil => XML.no_text
      case _ => err("multiple XML trees")
    }

  def parse_elem(
    source: Source,
    recode: String => String = identity,
    cache: XML.Cache = XML.Cache.none
  ): XML.Tree =
    parse_body(source, recode = recode, cache = cache) match {
      case List(elem: XML.Elem) => elem
      case _ => err("single XML element expected")
    }


  /* failsafe parsing */

  private def markup_broken(source: Source) =
    XML.Elem(Markup.Broken, List(XML.Text(source.toString)))

  def parse_body_failsafe(
    source: Source,
    recode: String => String = identity,
    cache: XML.Cache = XML.Cache.none
  ): XML.Body = {
    try { parse_body(source, recode = recode, cache = cache) }
    catch { case ERROR(_) => List(markup_broken(source)) }
  }

  def parse_failsafe(
    source: Source,
    recode: String => String = identity,
    cache: XML.Cache = XML.Cache.none
  ): XML.Tree = {
    try { parse(source, recode = recode, cache = cache) }
    catch { case ERROR(_) => markup_broken(source) }
  }
}
