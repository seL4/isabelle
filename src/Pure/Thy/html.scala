/*  Title:      Pure/Thy/html.scala
    Author:     Makarius

HTML presentation elements.
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


  // common markup elements

  def session_entry(name: String): String =
    XML.string_of_tree(
      XML.elem("li",
        List(XML.Elem(Markup("a", List(("href", name + "/index.html"))),
          List(XML.Text(name)))))) + "\n"

  def session_entries(names: List[String]): String =
    if (names.isEmpty) "</ul>"
    else
      "</ul>\n</div>\n<div class=\"sessions\">\n" +
      "<h2>Sessions</h2>\n<ul>\n" + names.map(session_entry).mkString + "</ul>";

  val end_document = "\n</div>\n</body>\n</html>\n"
}
