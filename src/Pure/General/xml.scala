/*  Title:      Pure/General/xml.scala
    ID:         $Id$
    Author:     Makarius

Simple XML tree values.
*/

package isabelle

import org.w3c.dom.{Node, Document}
import javax.xml.parsers.DocumentBuilderFactory


object XML {
  /* datatype representation */

  type Attributes = List[(String, String)]

  abstract class Tree
  case class Elem(name: String, attributes: Attributes, body: List[Tree]) extends Tree
  case class Text(content: String) extends Tree


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
      case Some((s, r)) => Some((s, r ::: ts))
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


  /* document object model (DOM) */

  def DOM(tree: Tree) = {
    val doc = DocumentBuilderFactory.newInstance.newDocumentBuilder.newDocument
    def dom_tree(tr: Tree): Node = tr match {
      case Elem(name, atts, ts) => {
        val node = doc.createElement(name)
        for ((name, value) <- atts) node.setAttribute(name, value)
        for (t <- ts) node.appendChild(dom_tree(t))
        node
      }
      case Text(txt) => doc.createTextNode(txt)
    }
    val root_elem = tree match {
      case Elem(_, _, _) => dom_tree(tree)
      case Text(_) => dom_tree(Elem("root", Nil, List(tree)))
    }
    doc.appendChild(root_elem)
    doc
  }

}
