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

  def span(cls: String, body: List[XML.Tree]): XML.Elem =
    XML.Elem(SPAN, List((CLASS, cls)), body)

  def hidden(txt: String): XML.Elem =
    span(Markup.HIDDEN, List(XML.Text(txt)))

  def sub(txt: String): XML.Elem = XML.elem("sub", List(XML.Text(txt)))
  def sup(txt: String): XML.Elem = XML.elem("sup", List(XML.Text(txt)))

  def spans(tree: XML.Tree): List[XML.Tree] =
    tree match {
      case XML.Elem(name, _, ts) => List(span(name, ts.flatMap(spans)))
      case XML.Text(txt) =>
        val ts = new ListBuffer[XML.Tree]
        val t = new StringBuilder
        def flush() {
          if (!t.isEmpty) {
            ts + XML.Text(t.toString)
            t.clear
          }
        }
        def add(elem: XML.Tree) {
          flush()
          ts + elem
        }
        val syms = Symbol.elements(txt)
        while (syms.hasNext) {
          val s1 = syms.next
          lazy val s2 = if (syms.hasNext) syms.next else ""
          s1 match {
            case "\n" => add(XML.elem(BR))
            case "\\<^bsub>" => t ++ s1  // FIXME
            case "\\<^esub>" => t ++ s1  // FIXME
            case "\\<^bsup>" => t ++ s1  // FIXME
            case "\\<^esup>" => t ++ s1  // FIXME
            case "\\<^sub>" | "\\<^isub>" => add(hidden(s1)); add(sub(s2))
            case "\\<^sup>" | "\\<^isup>" => add(hidden(s1)); add(sup(s2))
            case "\\<^bold>" => add(hidden(s1)); add(span("bold", List(XML.Text(s2))))
            case "\\<^loc>" => add(hidden(s1)); add(span("loc", List(XML.Text(s2))))
            case _ => t ++ s1
          }
        }
        flush()
        ts.toList
    }
}
