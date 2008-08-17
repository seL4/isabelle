/*  Title:      Pure/General/yxml.scala
    ID:         $Id$
    Author:     Makarius

Efficient text representation of XML trees.
*/

package isabelle

import java.util.regex.Pattern


object YXML {

  /* markers */

  private val X = '\5'
  private val Y = '\6'

  def detect(source: CharSequence) = {
    source.length >= 2 &&
    source.charAt(0) == X &&
    source.charAt(1) == Y
  }


  /* parsing */

  class BadYXML(msg: String) extends Exception

  private def err(msg: String) = throw new BadYXML(msg)
  private def err_attribute() = err("bad attribute")
  private def err_element() = err("bad element")
  private def err_unbalanced(name: String) =
    if (name == "") err("unbalanced element")
    else err("unbalanced element \"" + name + "\"")

  private val X_pattern = Pattern.compile(Pattern.quote(X.toString))
  private val Y_pattern = Pattern.compile(Pattern.quote(Y.toString))
  private val eq_pattern = Pattern.compile(Pattern.quote("="))

  private def parse_attrib(s: String) =
    eq_pattern.split(s, 2).toList match {
      case List(x, y) => if (x != "") (x, y) else err_attribute()
      case _ => err_attribute()
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
    for (chunk <- X_pattern.split(source) if chunk != "") {
      Y_pattern.split(chunk).toList match {
        case Nil => pop()
        case "" :: name :: atts => push(name, atts.map(parse_attrib))
        case txts => for (txt <- txts) add(XML.Text(txt))
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
