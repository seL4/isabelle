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


  // document markup

  def span(cls: String, body: XML.Body): XML.Elem =
    XML.Elem(Markup(SPAN, List((CLASS, cls))), body)

  def hidden(txt: String): XML.Elem =
    span(Markup.HIDDEN, List(XML.Text(txt)))

  def sub(txt: String): XML.Elem = XML.elem("sub", List(XML.Text(txt)))
  def sup(txt: String): XML.Elem = XML.elem("sup", List(XML.Text(txt)))

  def spans(symbols: Symbol.Interpretation,
    input: XML.Tree, original_data: Boolean = false): XML.Body =
  {
    def html_spans(tree: XML.Tree): XML.Body =
      tree match {
        case XML.Elem(Markup(name, _), ts) =>
          if (original_data)
            List(XML.Elem(Markup.Data, List(tree, span(name, ts.flatMap(html_spans)))))
          else List(span(name, ts.flatMap(html_spans)))
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
          val syms = Symbol.iterator(txt).map(_.toString)
          while (syms.hasNext) {
            val s1 = syms.next
            def s2() = if (syms.hasNext) syms.next else ""
            if (s1 == "\n") add(XML.elem(BR))
            else if (symbols.is_subscript_decoded(s1)) { add(hidden(s1)); add(sub(s2())) }
            else if (symbols.is_superscript_decoded(s1)) { add(hidden(s1)); add(sup(s2())) }
            else if (s1 == "\\<^bsub>") t ++= s1  // FIXME
            else if (s1 == "\\<^esub>") t ++= s1  // FIXME
            else if (s1 == "\\<^bsup>") t ++= s1  // FIXME
            else if (s1 == "\\<^esup>") t ++= s1  // FIXME
            else if (symbols.is_bold_decoded(s1)) {
              add(hidden(s1)); add(span("bold", List(XML.Text(s2()))))
            }
            else t ++= s1
          }
          flush()
          ts.toList
      }
    html_spans(input)
  }
}
