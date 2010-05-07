/*  Title:      Pure/General/pretty.scala
    Author:     Makarius

Generic pretty printing module.
*/

package isabelle


object Pretty
{
  /* markup trees with physical blocks and breaks */

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

  val FBreak = XML.Text("\n")


  /* formatted output */

  private case class Text(tx: List[String] = Nil, val pos: Int = 0, val nl: Int = 0)
  {
    def newline: Text = copy(tx = "\n" :: tx, pos = 0, nl = nl + 1)
    def string(s: String): Text = copy(tx = s :: tx, pos = pos + s.length)
    def blanks(wd: Int): Text = string(" " * wd)
    def content: String = tx.reverse.mkString
  }

  private def breakdist(trees: List[XML.Tree], after: Int): Int =
    trees match {
      case Break(_) :: _ => 0
      case FBreak :: _ => 0
      case XML.Elem(_, _, body) :: ts =>
        (0 /: body)(_ + XML.content_length(_)) + breakdist(ts, after)
      case XML.Text(s) :: ts => s.length + breakdist(ts, after)
      case Nil => after
    }

  private def forcenext(trees: List[XML.Tree]): List[XML.Tree] =
    trees match {
      case Nil => Nil
      case FBreak :: _ => trees
      case Break(_) :: ts => FBreak :: ts
      case t :: ts => t :: forcenext(ts)
    }

  private def standard(tree: XML.Tree): List[XML.Tree] =
    tree match {
      case XML.Elem(name, atts, body) => List(XML.Elem(name, atts, body.flatMap(standard)))
      case XML.Text(text) =>
        Library.separate(FBreak,
          Library.chunks(text).toList.map((s: CharSequence) => XML.Text(s.toString)))
    }

  def string_of(input: List[XML.Tree], margin: Int = 76): String =
  {
    val breakgain = margin / 20
    val emergencypos = margin / 2

    def format(trees: List[XML.Tree], blockin: Int, after: Int, text: Text): Text =
      trees match {
        case Nil => text

        case Block(indent, body) :: ts =>
          val pos1 = text.pos + indent
          val pos2 = pos1 % emergencypos
          val blockin1 =
            if (pos1 < emergencypos) pos1
            else pos2
          val btext = format(body, blockin1, breakdist(ts, after), text)
          val ts1 = if (text.nl < btext.nl) forcenext(ts) else ts
          format(ts1, blockin, after, btext)

        case Break(wd) :: ts =>
          if (text.pos + wd <= (margin - breakdist(ts, after)).max(blockin + breakgain))
            format(ts, blockin, after, text.blanks(wd))
          else format(ts, blockin, after, text.newline.blanks(blockin))
        case FBreak :: ts => format(ts, blockin, after, text.newline.blanks(blockin))

        case XML.Elem(_, _, body) :: ts => format(body ::: ts, blockin, after, text)
        case XML.Text(s) :: ts => format(ts, blockin, after, text.string(s))
      }
    format(input.flatMap(standard), 0, 0, Text()).content
  }
}
