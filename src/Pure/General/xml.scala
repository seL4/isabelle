/*  Title:      Pure/General/xml.scala
    ID:         $Id$
    Author:     Makarius

Minimalistic XML tree values.
*/

package isabelle

object XML {
  type Attributes = List[(String, String)]

  abstract class Tree
  case class Elem(name: String, attributes: Attributes, body: List[Tree]) extends Tree
  case class Text(content: String) extends Tree
}
