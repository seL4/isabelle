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
    def output_char(c: Char) =
      c match {
        case '<' => s ++= "&lt;"
        case '>' => s ++= "&gt;"
        case '&' => s ++= "&amp;"
        case '"' => s ++= "&quot;"
        case '\'' => s ++= "&#39;"
        case '\n' => s ++= "<br/>"
        case _ => s += c
      }
    def output_chars(str: String) = str.iterator.foreach(output_char(_))

    var ctrl = ""
    for (sym <- Symbol.iterator(text)) {
      if (control.isDefinedAt(sym)) ctrl = sym
      else {
        control.get(ctrl) match {
          case Some(elem) if Symbol.is_controllable(sym) && sym != "\"" =>
            s ++= ("<" + elem + ">")
            output_chars(sym)
            s ++= ("</" + elem + ">")
          case _ =>
            output_chars(ctrl)
            output_chars(sym)
        }
        ctrl = ""
      }
    }
    output_chars(ctrl)
  }

  def output(text: String): String = Library.make_string(output(text, _))


  /* output XML as HTML */

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
          s ++= "<"; elem(markup); s ++= ">"
          ts.foreach(tree)
          s ++= "</"; s ++= markup.name; s ++= ">"
        case XML.Text(txt) => output(txt, s)
      }
    body.foreach(tree)
  }

  def output(body: XML.Body): String = Library.make_string(output(body, _))
  def output(tree: XML.Tree): String = output(List(tree))


  /* markup operators */

  type Operator = XML.Body => XML.Elem

  val chapter: Operator = XML.elem("h1", _)
  val section: Operator = XML.elem("h2", _)
  val subsection: Operator = XML.elem("h3", _)
  val subsubsection: Operator = XML.elem("h4", _)
  val paragraph: Operator = XML.elem("h5", _)
  val subparagraph: Operator = XML.elem("h6", _)


  /* document */

  def begin_document(title: String): String =
    "<?xml version=\"1.0\" encoding=\"utf-8\" ?>\n" +
    "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\" " +
    "\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\">\n" +
    "<html xmlns=\"http://www.w3.org/1999/xhtml\">\n" +
    "<head>\n" +
    "<meta http-equiv=\"Content-Type\" content=\"text/html; charset=utf-8\"/>\n" +
    "<title>" + output(title + " (" + Distribution.version + ")") + "</title>\n" +
    "<link media=\"all\" rel=\"stylesheet\" type=\"text/css\" href=\"isabelle.css\"/>\n" +
    "</head>\n" +
    "\n" +
    "<body>\n" +
    "<div class=\"head\">" +
    "<h1>" + output(title) + "</h1>\n"

  val end_document = "\n</div>\n</body>\n</html>\n"


  /* common markup elements */

  private def session_entry(entry: (String, String)): String =
  {
    val (name, description) = entry
    val descr =
      if (description == "") Nil
      else List(XML.elem("br"), XML.elem("pre", List(XML.Text(description))))
    XML.string_of_tree(
      XML.elem("li",
        List(XML.Elem(Markup("a", List(("href", name + "/index.html"))),
          List(XML.Text(name)))) ::: descr)) + "\n"
  }

  def chapter_index(chapter: String, sessions: List[(String, String)]): String =
  {
    begin_document("Isabelle/" + chapter + " sessions") +
      (if (sessions.isEmpty) ""
       else "<div class=\"sessions\"><ul>\n" + sessions.map(session_entry(_)).mkString + "</ul>") +
    end_document
  }
}
