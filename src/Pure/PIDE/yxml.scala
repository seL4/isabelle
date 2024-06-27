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

  class Output_String(builder: StringBuilder) extends Output {
    override def byte(b: Byte): Unit = { builder += b.toChar }
    override def string(s: String): Unit = { builder ++= s }
    def result(ts: List[XML.Tree]): String = { traverse(ts); builder.toString }
  }

  class Output_Bytes(builder: Bytes.Builder) extends Output {
    override def byte(b: Byte): Unit = { builder += b }
    override def string(s: String): Unit = { builder += s }
  }

  def string_of_body(body: XML.Body): String =
    new Output_String(new StringBuilder).result(body)

  def string_of_tree(tree: XML.Tree): String = string_of_body(List(tree))

  def bytes_of_body(body: XML.Body): Bytes =
    Bytes.Builder.use()(builder => new Output_Bytes(builder).traverse(body))

  def bytes_of_tree(tree: XML.Tree): Bytes = bytes_of_body(List(tree))


  /* parsing */

  private def err(msg: String) = error("Malformed YXML: " + msg)
  private def err_attribute() = err("bad attribute")
  private def err_element() = err("bad element")
  private def err_unbalanced(name: String) =
    if (name == "") err("unbalanced element")
    else err("unbalanced element " + quote(name))

  private def parse_attrib(source: CharSequence): (String, String) =
    Properties.Eq.unapply(source.toString) getOrElse err_attribute()


  def parse_body(source: CharSequence, cache: XML.Cache = XML.Cache.none): XML.Body = {
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

    for (chunk <- Library.separated_chunks(is_X, source) if chunk.length != 0) {
      if (chunk.length == 1 && chunk.charAt(0) == Y) pop()
      else {
        Library.separated_chunks(is_Y, chunk).toList match {
          case ch :: name :: atts if ch.length == 0 =>
            push(name.toString, atts.map(parse_attrib))
          case txts => for (txt <- txts) add(cache.tree0(XML.Text(cache.string(txt.toString))))
        }
      }
    }
    (stack: @unchecked) match {
      case List((Markup.Empty, body)) => body.toList
      case (Markup(name, _), _) :: _ => err_unbalanced(name)
    }
  }

  def parse(source: CharSequence, cache: XML.Cache = XML.Cache.none): XML.Tree =
    parse_body(source, cache = cache) match {
      case List(result) => result
      case Nil => XML.no_text
      case _ => err("multiple XML trees")
    }

  def parse_elem(source: CharSequence, cache: XML.Cache = XML.Cache.none): XML.Tree =
    parse_body(source, cache = cache) match {
      case List(elem: XML.Elem) => elem
      case _ => err("single XML element expected")
    }


  /* failsafe parsing */

  private def markup_broken(source: CharSequence) =
    XML.Elem(Markup.Broken, List(XML.Text(source.toString)))

  def parse_body_failsafe(source: CharSequence, cache: XML.Cache = XML.Cache.none): XML.Body = {
    try { parse_body(source, cache = cache) }
    catch { case ERROR(_) => List(markup_broken(source)) }
  }

  def parse_failsafe(source: CharSequence, cache: XML.Cache = XML.Cache.none): XML.Tree = {
    try { parse(source, cache = cache) }
    catch { case ERROR(_) => markup_broken(source) }
  }
}
