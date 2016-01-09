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

  def output(text: String): String =
  {
    val result = new StringBuilder

    def output_char(c: Char) =
      c match {
        case '<' => result ++= "&lt;"
        case '>' => result ++= "&gt;"
        case '&' => result ++= "&amp;"
        case '"' => result ++= "&quot;"
        case '\'' => result ++= "&#39;"
        case '\n' => result ++= "<br/>"
        case _ => result += c
      }
    def output_chars(s: String) = s.iterator.foreach(output_char(_))

    var ctrl = ""
    for (sym <- Symbol.iterator(text)) {
      if (control.isDefinedAt(sym)) ctrl = sym
      else {
        control.get(ctrl) match {
          case Some(elem) if Symbol.is_controllable(sym) && sym != "\"" =>
            result ++= ("<" + elem + ">")
            output_chars(sym)
            result ++= ("</" + elem + ">")
          case _ =>
            output_chars(ctrl)
            output_chars(sym)
        }
        ctrl = ""
      }
    }
    output_chars(ctrl)

    result.toString
  }


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
