/*  Title:      Tools/VSCode/extension/src/dom_metric.scala
    Author:     Fabian Huch

Pretty-printing metric based on DOM rendering of symbol codepoints.
*/

package isabelle.vscode.extension

import org.scalajs.dom

import isabelle._


object DOM_Metric {
  private def string_bounds(s: String): dom.DOMRect = {
    val span = dom.document.createElement("span")
    span.setAttribute("class", "source")
    span.setAttribute("style", "white-space: pre-wrap;")
    span.textContent = s

    dom.document.body.appendChild(span)
    val res = span.getBoundingClientRect()
    dom.document.body.removeChild(span)

    res
  }

  def string_width(s: String): Double = string_bounds(s).width
  def space_width(): Double = string_width(Symbol.space)

  private val sample = "mix"
  def average_width(): Double = string_width(sample) / sample.length

  private def px(s: String): Int = Value.Int.parse(Library.perhaps_unsuffix("px", s))
  def content_width(elem: dom.HTMLElement = dom.document.body): Double = {
    val style = dom.window.getComputedStyle(elem)
    val padding = px(style.paddingLeft) + px(style.paddingRight)
    elem.clientWidth - padding
  }

  def apply(): DOM_Metric = {
    val codepoints =
      Symbol.symbols.entries.flatMap(_.code) :::
        (0 until 128).filter(i => Symbol.is_ascii_printable(i.toChar)).toList

    val codepoint_widths = for (c <- codepoints) yield c -> string_width(Codepoint.string(c))
    new DOM_Metric(average_width(), codepoint_widths.toMap)
  }

  def unit(): Double = space_width() max 1.0
  def average(): Double = average_width() / unit()
  def content(elem: dom.HTMLElement = dom.document.body): Double = content_width(elem) / unit()
}

class DOM_Metric private(val average_width: Double, codepoint_widths: Map[Int, Double])
  extends Pretty.Metric {

  def string_width(s: String): Double =
    Codepoint.iterator(s).map(codepoint_widths.getOrElse(_, average_width)).sum

  val unit = string_width(Symbol.space) max 1.0
  def apply(s: String) = string_width(s) / unit

  def content(elem: dom.HTMLElement = dom.document.body): Double =
    DOM_Metric.content_width(elem) / unit
}
