/*  Title:      Pure/General/yxml.scala
    ID:         $Id$
    Author:     Makarius

Efficient text representation of XML trees.
*/

package isabelle

import java.util.regex.Pattern


object YXML {

  /* chunk markers */

  private val X = '\5'
  private val Y = '\6'

  def detect(source: CharSequence) = {
    source.length >= 2 &&
    source.charAt(0) == X &&
    source.charAt(1) == Y
  }


  /* iterate over chunks (resembles space_explode in ML) */

  private def chunks(sep: Char, source: CharSequence) = new Iterator[CharSequence] {
    private val end = source.length
    private var state = if (end == 0) None else get_chunk(-1)
    private def get_chunk(i: Int) = {
      if (i < end) {
        var j = i; do j += 1 while (j < end && source.charAt(j) != sep)
        Some((source.subSequence(i + 1, j), j))
      }
      else None
    }

    def hasNext() = state.isDefined
    def next() = state match {
      case Some((s, i)) => { state = get_chunk(i); s }
      case None => throw new NoSuchElementException("next on empty iterator")
    }
  }


  /* parsing */

  class BadYXML(msg: String) extends Exception

  private def err(msg: String) = throw new BadYXML(msg)
  private def err_attribute() = err("bad attribute")
  private def err_element() = err("bad element")
  private def err_unbalanced(name: String) =
    if (name == "") err("unbalanced element")
    else err("unbalanced element \"" + name + "\"")

  private def parse_attrib(source: CharSequence) = {
    val s = source.toString
    val i = s.indexOf('=')
    if (i <= 0) err_attribute()
    (s.substring(0, i - 1), s.substring(i + 1))
  }


  def parse_body(source: CharSequence) = {

    /* stack operations */

    var stack: List[((String, XML.Attributes), List[XML.Tree])] = null

    def add(x: XML.Tree) = stack match {
      case ((elem, body) :: pending) => stack = (elem, x :: body) :: pending
    }

    def push(name: String, atts: XML.Attributes) =
      if (name == "") err_element()
      else stack = ((name, atts), Nil) :: stack

    def pop() = stack match {
      case ((("", _), _) :: _) => err_unbalanced("")
      case (((name, atts), body) :: pending) =>
        stack = pending; add(XML.Elem(name, atts, body.reverse))
    }


    /* parse chunks */

    stack = List((("", Nil), Nil))
    for (chunk <- chunks(X, source) if chunk != "") {
      chunks(Y, chunk).toList match {
        case List("", "") => pop()
        case "" :: name :: atts => push(name.toString, atts.map(parse_attrib))
        case txts => for (txt <- txts) add(XML.Text(txt.toString))
      }
    }
    stack match {
      case List((("", _), result)) => result.reverse
      case ((name, _), _) :: _ => err_unbalanced(name)
    }
  }

  def parse(source: CharSequence) =
    parse_body(source) match {
      case List(result) => result
      case Nil => XML.Text("")
      case _ => err("multiple results")
    }
}
