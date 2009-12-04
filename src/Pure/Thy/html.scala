/*  Title:      Pure/Thy/html.scala
    Author:     Makarius

Basic HTML output.
*/

package isabelle

object HTML
{
  // common elements and attributes

  val BODY = "body"
  val DIV = "div"
  val SPAN = "span"
  val BR = "br"
  val CLASS = "class"


  // document markup

  def body(trees: List[XML.Tree]): XML.Tree =
    XML.Elem(BODY, Nil, trees)

  def div(trees: List[XML.Tree]): XML.Tree =
    XML.Elem(DIV, Nil, trees)

  val br: XML.Tree = XML.Elem(BR, Nil, Nil)

  def spans(tree: XML.Tree): List[XML.Tree] =
    tree match {
      case XML.Elem(name, _, ts) =>
        List(XML.Elem(SPAN, List((CLASS, name)), ts.flatMap(spans)))
      case text @ XML.Text(txt) =>
        txt.split("\n").toList match {
          case line :: lines if !lines.isEmpty =>
            XML.Text(line) :: lines.flatMap(l => List(br, XML.Text(l)))
          case _ => List(text)
        }
    }
}
