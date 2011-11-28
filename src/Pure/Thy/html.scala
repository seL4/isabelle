/*  Title:      Pure/Thy/html.scala
    Author:     Makarius

Basic HTML output.
*/

package isabelle

import scala.collection.mutable.ListBuffer


object HTML
{
  // encode text

  def encode(text: String): String =
  {
    val s = new StringBuilder
    for (c <- text.iterator) c match {
      case '<' => s ++= "&lt;"
      case '>' => s ++= "&gt;"
      case '&' => s ++= "&amp;"
      case '"' => s ++= "&quot;"
      case '\'' => s ++= "&#39;"
      case '\n' => s ++= "<br/>"
      case _ => s += c
    }
    s.toString
  }


  // common elements and attributes

  val BODY = "body"
  val DIV = "div"
  val SPAN = "span"
  val BR = "br"
  val PRE = "pre"
  val CLASS = "class"
  val STYLE = "style"


  // document markup

  def span(cls: String, body: XML.Body): XML.Elem =
    XML.Elem(Markup(SPAN, List((CLASS, cls))), body)

  def user_font(font: String, txt: String): XML.Elem =
    XML.Elem(Markup(SPAN, List((STYLE, "font-family: " + font))), List(XML.Text(txt)))

  def hidden(txt: String): XML.Elem =
    span(Isabelle_Markup.HIDDEN, List(XML.Text(txt)))

  def sub(txt: String): XML.Elem = XML.elem("sub", List(XML.Text(txt)))
  def sup(txt: String): XML.Elem = XML.elem("sup", List(XML.Text(txt)))
  def bold(txt: String): XML.Elem = span("bold", List(XML.Text(txt)))

  def spans(input: XML.Tree, original_data: Boolean = false): XML.Body =
  {
    def html_spans(tree: XML.Tree): XML.Body =
      tree match {
        case XML.Elem(m @ Markup(name, props), ts) =>
          val span_class =
            m match { case Isabelle_Markup.Entity(kind, _) => name + "_" + kind case _ => name }
          val html_span = span(span_class, ts.flatMap(html_spans))
          if (original_data) List(XML.Elem(Markup.Data, List(tree, html_span)))
          else List(html_span)
        case XML.Text(txt) =>
          val ts = new ListBuffer[XML.Tree]
          val t = new StringBuilder
          def flush() {
            if (!t.isEmpty) {
              ts += XML.Text(t.toString)
              t.clear
            }
          }
          def add(elem: XML.Tree) {
            flush()
            ts += elem
          }
          val syms = Symbol.iterator(txt)
          while (syms.hasNext) {
            val s1 = syms.next
            def s2() = if (syms.hasNext) syms.next else ""
            if (s1 == "\n") add(XML.elem(BR))
            else if (s1 == Symbol.sub_decoded || s1 == Symbol.isub_decoded)
              { add(hidden(s1)); add(sub(s2())) }
            else if (s1 == Symbol.sup_decoded || s1 == Symbol.isup_decoded)
              { add(hidden(s1)); add(sup(s2())) }
            else if (s1 == Symbol.bsub_decoded) t ++= s1  // FIXME
            else if (s1 == Symbol.esub_decoded) t ++= s1  // FIXME
            else if (s1 == Symbol.bsup_decoded) t ++= s1  // FIXME
            else if (s1 == Symbol.esup_decoded) t ++= s1  // FIXME
            else if (s1 == Symbol.bold_decoded) { add(hidden(s1)); add(bold(s2())) }
            else if (Symbol.fonts.isDefinedAt(s1)) { add(user_font(Symbol.fonts(s1), s1)) }
            else t ++= s1
          }
          flush()
          ts.toList
      }
    html_spans(input)
  }
}
