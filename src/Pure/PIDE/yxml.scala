/*  Title:      Pure/PIDE/yxml.scala
    Author:     Makarius

Efficient text representation of XML trees.  Suitable for direct
inlining into plain text.
*/

package isabelle


import scala.collection.mutable


object YXML
{
  /* chunk markers */

  val X = '\u0005'
  val Y = '\u0006'

  val is_X: Char => Boolean = _ == X
  val is_Y: Char => Boolean = _ == Y

  val X_string: String = X.toString
  val Y_string: String = Y.toString
  val XY_string: String = X_string + Y_string
  val XYX_string: String = XY_string + X_string

  def detect(s: String): Boolean = s.exists(c => c == X || c == Y)
  def detect_elem(s: String): Boolean = s.startsWith(XY_string)


  /* string representation */

  def traversal(string: String => Unit, body: XML.Body): Unit =
  {
    def tree(t: XML.Tree): Unit =
      t match {
        case XML.Elem(markup @ Markup(name, atts), ts) =>
          if (markup.is_empty) ts.foreach(tree)
          else {
            string(XY_string)
            string(name)
            for ((a, x) <- atts) { string(Y_string); string(a); string("="); string(x) }
            string(X_string)
            ts.foreach(tree)
            string(XYX_string)
          }
        case XML.Text(text) => string(text)
      }
    body.foreach(tree)
  }

  def string_of_body(body: XML.Body): String =
  {
    val s = new StringBuilder
    traversal(str => s ++= str, body)
    s.toString
  }

  def string_of_tree(tree: XML.Tree): String = string_of_body(List(tree))


  /* parsing */

  private def err(msg: String) = error("Malformed YXML: " + msg)
  private def err_attribute() = err("bad attribute")
  private def err_element() = err("bad element")
  private def err_unbalanced(name: String) =
    if (name == "") err("unbalanced element")
    else err("unbalanced element " + quote(name))

  private def parse_attrib(source: CharSequence): (String, String) =
  {
    val s = source.toString
    val i = s.indexOf('=')
    if (i <= 0) err_attribute()
    (s.substring(0, i), s.substring(i + 1))
  }


  def parse_body(source: CharSequence, cache: XML.Cache = XML.Cache.none): XML.Body =
  {
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

  def parse_body_failsafe(source: CharSequence, cache: XML.Cache = XML.Cache.none): XML.Body =
  {
    try { parse_body(source, cache = cache) }
    catch { case ERROR(_) => List(markup_broken(source)) }
  }

  def parse_failsafe(source: CharSequence, cache: XML.Cache = XML.Cache.none): XML.Tree =
  {
    try { parse(source, cache = cache) }
    catch { case ERROR(_) => markup_broken(source) }
  }
}
