/*  Title:      Pure/General/output.scala
    Author:     Makarius

Prover output messages.
*/

package isabelle


object Output
{
  object Message
  {
    def apply(name: String, atts: XML.Attributes, body: List[XML.Tree]): XML.Tree =
      XML.Elem(Markup.MESSAGE, (Markup.CLASS, name) :: atts, body)

    def unapply(tree: XML.Tree): Option[(String, XML.Attributes, List[XML.Tree])] =
      tree match {
        case XML.Elem(Markup.MESSAGE, (Markup.CLASS, name) :: atts, body) =>
          Some(name, atts, body)
        case _ => None
      }
  }
}
