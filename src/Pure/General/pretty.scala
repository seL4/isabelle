/*  Title:      Pure/General/pretty.scala
    Author:     Makarius

Symbolic pretty printing.
*/

package isabelle


object Pretty
{
  object Block
  {
    def apply(indent: Int, body: List[XML.Tree]): XML.Tree =
      XML.Elem(Markup.BLOCK, List((Markup.INDENT, indent.toString)), body)

    def unapply(tree: XML.Tree): Option[(Int, List[XML.Tree])] =
      tree match {
        case XML.Elem(Markup.BLOCK, List((Markup.INDENT, indent)), body) =>
          Markup.parse_int(indent) match {
            case Some(i) => Some((i, body))
            case None => None
          }
        case _ => None
      }
  }

  object Break
  {
    def apply(width: Int): XML.Tree =
      XML.Elem(Markup.BREAK, List((Markup.WIDTH, width.toString)), List(XML.Text(" " * width)))

    def unapply(tree: XML.Tree): Option[Int] =
      tree match {
        case XML.Elem(Markup.BREAK, List((Markup.WIDTH, width)), _) => Markup.parse_int(width)
        case _ => None
      }
  }

  object FBreak
  {
    def apply(): XML.Tree = XML.Elem(Markup.FBREAK, Nil, List(XML.Text(" ")))

    def unapply(tree: XML.Tree): Boolean =
      tree match {
        case XML.Elem(Markup.FBREAK, Nil, _) => true
        case _ => false
      }
  }
}
