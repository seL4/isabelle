/*  Title:      Pure/General/xml.scala
    Author:     Makarius

Simple XML tree values.
*/

package isabelle

import org.w3c.dom.{Node, Document}
import javax.xml.parsers.DocumentBuilderFactory


object XML
{
  /* datatype representation */

  type Attributes = List[(String, String)]

  sealed abstract class Tree {
    override def toString = {
      val s = new StringBuilder
      append_tree(this, s)
      s.toString
    }
  }
  case class Elem(name: String, attributes: Attributes, body: List[Tree]) extends Tree
  case class Text(content: String) extends Tree

  def elem(name: String, body: List[Tree]) = Elem(name, Nil, body)
  def elem(name: String) = Elem(name, Nil, Nil)


  /* string representation */

  private def append_text(text: String, s: StringBuilder) {
    if (text == null) s ++ text
    else {
      for (c <- text.elements) c match {
        case '<' => s ++ "&lt;"
        case '>' => s ++ "&gt;"
        case '&' => s ++ "&amp;"
        case '"' => s ++ "&quot;"
        case '\'' => s ++ "&apos;"
        case _ => s + c
      }
    }
  }

  private def append_elem(name: String, atts: Attributes, s: StringBuilder) {
    s ++ name
    for ((a, x) <- atts) {
      s ++ " "; s ++ a; s ++ "=\""; append_text(x, s); s ++ "\""
    }
  }

  private def append_tree(tree: Tree, s: StringBuilder) {
    tree match {
      case Elem(name, atts, Nil) =>
        s ++ "<"; append_elem(name, atts, s); s ++ "/>"
      case Elem(name, atts, ts) =>
        s ++ "<"; append_elem(name, atts, s); s ++ ">"
        for (t <- ts) append_tree(t, s)
        s ++ "</"; s ++ name; s ++ ">"
      case Text(text) => append_text(text, s)
    }
  }


  /* iterate over content */

  private type State = Option[(String, List[Tree])]

  private def get_next(tree: Tree): State = tree match {
    case Elem(_, _, body) => get_nexts(body)
    case Text(content) => Some(content, Nil)
  }
  private def get_nexts(trees: List[Tree]): State = trees match {
    case Nil => None
    case t :: ts => get_next(t) match {
      case None => get_nexts(ts)
      case Some((s, r)) => Some((s, r ++ ts))
    }
  }

  def content(tree: Tree) = new Iterator[String] {
    private var state = get_next(tree)
    def hasNext() = state.isDefined
    def next() = state match {
      case Some((s, rest)) => { state = get_nexts(rest); s }
      case None => throw new NoSuchElementException("next on empty iterator")
    }
  }


  /* document object model (W3C DOM) */

  def document_node(doc: Document, tree: Tree): Node =
  {
    def DOM(tr: Tree): Node = tr match {
      case Elem(Markup.DATA, Nil, List(data, t)) =>
        val node = DOM(t)
        node.setUserData(Markup.DATA, data, null)
        node
      case Elem(name, atts, ts) =>
        if (name == Markup.DATA)
          error("Malformed data element: " + tr.toString)
        val node = doc.createElement(name)
        for ((name, value) <- atts) node.setAttribute(name, value)
        for (t <- ts) node.appendChild(DOM(t))
        node
      case Text(txt) => doc.createTextNode(txt)
    }
    DOM(tree)
  }

  def document(tree: Tree, styles: String*): Document =
  {
    val doc = DocumentBuilderFactory.newInstance.newDocumentBuilder.newDocument
    doc.appendChild(doc.createProcessingInstruction("xml", "version=\"1.0\""))

    for (style <- styles) {
      doc.appendChild(doc.createProcessingInstruction("xml-stylesheet",
        "href=\"" + style + "\" type=\"text/css\""))
    }
    val root_elem = tree match {
      case Elem(_, _, _) => document_node(doc, tree)
      case Text(_) => document_node(doc, (Elem(Markup.ROOT, Nil, List(tree))))
    }
    doc.appendChild(root_elem)
    doc
  }
}
