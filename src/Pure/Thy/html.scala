/*  Title:      Pure/Thy/html.scala
    Author:     Makarius

HTML presentation elements.
*/

package isabelle


object HTML
{
  /* encode text with control symbols */

  val control =
    Map(
      Symbol.sub -> "sub",
      Symbol.sub_decoded -> "sub",
      Symbol.sup -> "sup",
      Symbol.sup_decoded -> "sup",
      Symbol.bold -> "b",
      Symbol.bold_decoded -> "b")

  def output(text: String, s: StringBuilder)
  {
    def output_string(str: String) = XML.output_string(str, s)

    var ctrl = ""
    for (sym <- Symbol.iterator(text)) {
      if (control.isDefinedAt(sym)) ctrl = sym
      else {
        control.get(ctrl) match {
          case Some(elem) if Symbol.is_controllable(sym) && sym != "\"" =>
            s ++= ("<" + elem + ">")
            output_string(sym)
            s ++= ("</" + elem + ">")
          case _ =>
            output_string(ctrl)
            output_string(sym)
        }
        ctrl = ""
      }
    }
    output_string(ctrl)
  }

  def output(text: String): String = Library.make_string(output(text, _))


  /* output XML as HTML */

  private val structural_elements =
    Set("head", "body", "meta", "div", "pre", "p", "title", "h1", "h2", "h3", "h4", "h5", "h6",
      "ul", "ol", "dl", "li", "dt", "dd")

  def output(body: XML.Body, s: StringBuilder)
  {
    def attrib(p: (String, String)): Unit =
      { s ++= " "; s ++= p._1; s ++= "=\""; output(p._2, s); s ++= "\"" }
    def elem(markup: Markup): Unit =
      { s ++= markup.name; markup.properties.foreach(attrib) }
    def tree(t: XML.Tree): Unit =
      t match {
        case XML.Elem(markup, Nil) =>
          s ++= "<"; elem(markup); s ++= "/>"
        case XML.Elem(markup, ts) =>
          if (structural_elements(markup.name)) s += '\n'
          s ++= "<"; elem(markup); s ++= ">"
          ts.foreach(tree)
          s ++= "</"; s ++= markup.name; s ++= ">"
          if (structural_elements(markup.name)) s += '\n'
        case XML.Text(txt) => output(txt, s)
      }
    body.foreach(tree)
  }

  def output(body: XML.Body): String = Library.make_string(output(body, _))
  def output(tree: XML.Tree): String = output(List(tree))


  /* attributes */

  class Attribute(name: String, value: String)
  { def apply(elem: XML.Elem): XML.Elem = elem + (name -> value) }

  def id(s: String) = new Attribute("id", s)
  def css_class(name: String) = new Attribute("class", name)

  def width(w: Int) = new Attribute("width", w.toString)
  def height(h: Int) = new Attribute("height", h.toString)
  def size(w: Int, h: Int)(elem: XML.Elem): XML.Elem = width(w)(height(h)(elem))


  /* structured markup operators */

  def text(txt: String): XML.Body = if (txt.isEmpty) Nil else List(XML.Text(txt))
  val break: XML.Body = List(XML.elem("br"))

  class Operator(name: String)
  { def apply(body: XML.Body): XML.Elem = XML.elem(name, body) }

  class Heading(name: String) extends Operator(name)
  { def apply(txt: String): XML.Elem = super.apply(text(txt)) }

  val div = new Operator("div")
  val span = new Operator("span")
  val pre = new Operator("pre")
  val par = new Operator("p")
  val emph = new Operator("em")
  val bold = new Operator("b")
  val code = new Operator("code")

  val title = new Heading("title")
  val chapter = new Heading("h1")
  val section = new Heading("h2")
  val subsection = new Heading("h3")
  val subsubsection = new Heading("h4")
  val paragraph = new Heading("h5")
  val subparagraph = new Heading("h6")

  def itemize(items: List[XML.Body]): XML.Elem =
    XML.elem("ul", items.map(XML.elem("li", _)))

  def enumerate(items: List[XML.Body]): XML.Elem =
    XML.elem("ol", items.map(XML.elem("li", _)))

  def description(items: List[(XML.Body, XML.Body)]): XML.Elem =
    XML.elem("dl", items.flatMap({ case (x, y) => List(XML.elem("dt", x), XML.elem("dd", y)) }))

  def link(href: String, body: XML.Body = Nil): XML.Elem =
    XML.Elem(Markup("a", List("href" -> href)), if (body.isEmpty) text(href) else body)

  def image(src: String, alt: String = ""): XML.Elem =
    XML.Elem(Markup("img", List("src" -> src) ::: proper_string(alt).map("alt" -> _).toList), Nil)

  def source(src: String): XML.Elem = css_class("source")(div(List(pre(text(src)))))

  def style(s: String): XML.Elem = XML.elem("style", text(s))


  /* messages */

  // background
  val writeln_message: Attribute = css_class("writeln_message")
  val warning_message: Attribute = css_class("warning_message")
  val error_message: Attribute = css_class("error_message")

  // underline
  val writeln: Attribute = css_class("writeln")
  val warning: Attribute = css_class("warning")
  val error: Attribute = css_class("error")


  /* tooltips */

  def tooltip(item: XML.Body, tip: XML.Body): XML.Elem =
    span(item ::: List(css_class("tooltip")(div(tip))))

  def tooltip_errors(item: XML.Body, msgs: List[XML.Body]): XML.Elem =
    HTML.error(tooltip(item, msgs.map(msg => error_message(pre(msg)))))


  /* document */

  val header: String =
    """<?xml version="1.0" encoding="utf-8" ?>
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">"""

  val head_meta: XML.Elem =
    XML.Elem(Markup("meta",
      List("http-equiv" -> "Content-Type", "content" -> "text/html; charset=utf-8")), Nil)

  def head_css(css: String): XML.Elem =
    XML.Elem(Markup("link", List("rel" -> "stylesheet", "type" -> "text/css", "href" -> css)), Nil)

  def output_document(head: XML.Body, body: XML.Body, css: String = "isabelle.css"): String =
    cat_lines(
      List(header,
        output(XML.elem("head", head_meta :: (if (css == "") Nil else List(head_css(css))) ::: head)),
        output(XML.elem("body", body))))


  /* document directory */

  def init_dir(dir: Path)
  {
    Isabelle_System.mkdirs(dir)
    File.copy(Path.explode("~~/etc/isabelle.css"), dir)
  }

  def write_document(dir: Path, name: String, head: XML.Body, body: XML.Body,
    css: String = "isabelle.css")
  {
    init_dir(dir)
    File.write(dir + Path.basic(name), output_document(head, body, css))
  }
}
