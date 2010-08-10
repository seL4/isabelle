/*  Title:      Pure/General/xml.scala
    Author:     Makarius

Simple XML tree values.
*/

package isabelle

import java.util.WeakHashMap
import java.lang.ref.WeakReference
import javax.xml.parsers.DocumentBuilderFactory


object XML
{
  /* datatype representation */

  type Attributes = List[(String, String)]

  sealed abstract class Tree { override def toString = string_of_tree(this) }
  case class Elem(markup: Markup, body: List[Tree]) extends Tree
  case class Text(content: String) extends Tree

  def elem(name: String, body: List[Tree]) = Elem(Markup(name, Nil), body)
  def elem(name: String) = Elem(Markup(name, Nil), Nil)

  type Body = List[Tree]


  /* string representation */

  def string_of_body(body: Body): String =
  {
    val s = new StringBuilder

    def text(txt: String) {
      if (txt == null) s ++= txt
      else {
        for (c <- txt.iterator) c match {
          case '<' => s ++= "&lt;"
          case '>' => s ++= "&gt;"
          case '&' => s ++= "&amp;"
          case '"' => s ++= "&quot;"
          case '\'' => s ++= "&apos;"
          case _ => s += c
        }
      }
    }
    def attrib(p: (String, String)) { s ++= " "; s ++= p._1; s ++= "=\""; text(p._2); s ++= "\"" }
    def elem(markup: Markup) { s ++= markup.name; markup.properties.foreach(attrib) }
    def tree(t: Tree): Unit =
      t match {
        case Elem(markup, Nil) =>
          s ++= "<"; elem(markup); s ++= "/>"
        case Elem(markup, ts) =>
          s ++= "<"; elem(markup); s ++= ">"
          ts.foreach(tree)
          s ++= "</"; s ++= markup.name; s ++= ">"
        case Text(txt) => text(txt)
      }
    body.foreach(tree)
    s.toString
  }

  def string_of_tree(tree: XML.Tree): String = string_of_body(List(tree))


  /* iterate over content */

  private type State = Option[(String, List[Tree])]

  private def get_next(tree: Tree): State = tree match {
    case Elem(_, body) => get_nexts(body)
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


  /* cache for partial sharing -- NOT THREAD SAFE */

  class Cache(initial_size: Int)
  {
    private val table = new WeakHashMap[Any, WeakReference[Any]](initial_size)

    private def lookup[A](x: A): Option[A] =
    {
      val ref = table.get(x)
      if (ref == null) None
      else {
        val y = ref.asInstanceOf[WeakReference[A]].get
        if (y == null) None
        else Some(y)
      }
    }
    private def store[A](x: A): A =
    {
      table.put(x, new WeakReference[Any](x))
      x
    }

    def cache_string(x: String): String =
      lookup(x) match {
        case Some(y) => y
        case None => store(new String(x.toCharArray))  // trim string value
      }
    def cache_props(x: List[(String, String)]): List[(String, String)] =
      if (x.isEmpty) x
      else
        lookup(x) match {
          case Some(y) => y
          case None => store(x.map(p => (cache_string(p._1), cache_string(p._2))))
        }
    def cache_markup(x: Markup): Markup =
      lookup(x) match {
        case Some(y) => y
        case None =>
          x match {
            case Markup(name, props) =>
              store(Markup(cache_string(name), cache_props(props)))
          }
      }
    def cache_tree(x: XML.Tree): XML.Tree =
      lookup(x) match {
        case Some(y) => y
        case None =>
          x match {
            case XML.Elem(markup, body) =>
              store(XML.Elem(cache_markup(markup), cache_trees(body)))
            case XML.Text(text) => store(XML.Text(cache_string(text)))
          }
      }
    def cache_trees(x: List[XML.Tree]): List[XML.Tree] =
      if (x.isEmpty) x
      else
        lookup(x) match {
          case Some(y) => y
          case None => x.map(cache_tree(_))
        }
  }


  /* document object model (W3C DOM) */

  def get_data(node: org.w3c.dom.Node): Option[XML.Tree] =
    node.getUserData(Markup.Data.name) match {
      case tree: XML.Tree => Some(tree)
      case _ => None
    }

  def document_node(doc: org.w3c.dom.Document, tree: Tree): org.w3c.dom.Node =
  {
    def DOM(tr: Tree): org.w3c.dom.Node = tr match {
      case Elem(Markup.Data, List(data, t)) =>
        val node = DOM(t)
        node.setUserData(Markup.Data.name, data, null)
        node
      case Elem(Markup(name, atts), ts) =>
        if (name == Markup.Data.name)
          error("Malformed data element: " + tr.toString)
        val node = doc.createElement(name)
        for ((name, value) <- atts) node.setAttribute(name, value)
        for (t <- ts) node.appendChild(DOM(t))
        node
      case Text(txt) => doc.createTextNode(txt)
    }
    DOM(tree)
  }
}
