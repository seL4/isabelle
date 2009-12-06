/*  Title:      Pure/Thy/html.scala
    Author:     Makarius

Basic HTML output.
*/

package isabelle

import scala.collection.mutable.ListBuffer


object HTML
{
  // common elements and attributes

  val BODY = "body"
  val DIV = "div"
  val SPAN = "span"
  val BR = "br"
  val PRE = "pre"
  val CLASS = "class"


  // document markup

  def spans(tree: XML.Tree): List[XML.Tree] =
    tree match {
      case XML.Elem(name, _, ts) =>
        List(XML.Elem(SPAN, List((CLASS, name)), ts.flatMap(spans)))
      case XML.Text(txt) =>
        val ts = new ListBuffer[XML.Tree]
        val t = new StringBuilder
        def flush_text() {
          if (!t.isEmpty) {
            ts + XML.Text(t.toString)
            t.clear
          }
        }
        for (sym <- Symbol.elements(txt)) {
          sym match {
            case "\n" =>
              flush_text()
              ts + XML.elem(BR)
            case _ =>
              t ++ sym.toString
          }
        }
        flush_text()
        ts.toList
    }
}
