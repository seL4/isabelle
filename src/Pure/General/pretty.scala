/*  Title:      Pure/General/pretty.scala
    Author:     Makarius

Generic pretty printing module.
*/

package isabelle


import java.awt.FontMetrics


object Pretty
{
  /* markup trees with physical blocks and breaks */

  def block(body: XML.Body): XML.Tree = Block(2, body)

  object Block
  {
    def apply(i: Int, body: XML.Body): XML.Tree =
      XML.Elem(Markup(Isabelle_Markup.BLOCK, Isabelle_Markup.Indent(i)), body)

    def unapply(tree: XML.Tree): Option[(Int, XML.Body)] =
      tree match {
        case XML.Elem(Markup(Isabelle_Markup.BLOCK, Isabelle_Markup.Indent(i)), body) =>
          Some((i, body))
        case _ => None
      }
  }

  object Break
  {
    def apply(w: Int): XML.Tree =
      XML.Elem(Markup(Isabelle_Markup.BREAK, Isabelle_Markup.Width(w)),
        List(XML.Text(Symbol.spaces(w))))

    def unapply(tree: XML.Tree): Option[Int] =
      tree match {
        case XML.Elem(Markup(Isabelle_Markup.BREAK, Isabelle_Markup.Width(w)), _) => Some(w)
        case _ => None
      }
  }

  val FBreak = XML.Text("\n")


  /* formatted output */

  private def standard_format(tree: XML.Tree): XML.Body =
    tree match {
      case XML.Elem(markup, body) => List(XML.Elem(markup, body.flatMap(standard_format)))
      case XML.Text(text) =>
        Library.separate(FBreak,
          Library.chunks(text).toList.map((s: CharSequence) => XML.Text(s.toString)))
    }

  private sealed case class Text(tx: XML.Body = Nil, val pos: Double = 0.0, val nl: Int = 0)
  {
    def newline: Text = copy(tx = FBreak :: tx, pos = 0.0, nl = nl + 1)
    def string(s: String, len: Double): Text = copy(tx = XML.Text(s) :: tx, pos = pos + len)
    def blanks(wd: Int): Text = string(Symbol.spaces(wd), wd.toDouble)
    def content: XML.Body = tx.reverse
  }

  private val margin_default = 76
  private def metric_default(s: String) = s.length.toDouble

  def font_metric(metrics: FontMetrics): String => Double =
    if (metrics == null) ((s: String) => s.length.toDouble)
    else {
      val unit = metrics.charWidth(Symbol.spc).toDouble
      ((s: String) => if (s == "\n") 1.0 else metrics.stringWidth(s) / unit)
    }

  def formatted(input: XML.Body, margin: Int = margin_default,
    metric: String => Double = metric_default): XML.Body =
  {
    val breakgain = margin / 20
    val emergencypos = margin / 2

    def content_length(tree: XML.Tree): Double =
      tree match {
        case XML.Elem(_, body) => (0.0 /: body)(_ + content_length(_))
        case XML.Text(s) => metric(s)
      }

    def breakdist(trees: XML.Body, after: Double): Double =
      trees match {
        case Break(_) :: _ => 0.0
        case FBreak :: _ => 0.0
        case t :: ts => content_length(t) + breakdist(ts, after)
        case Nil => after
      }

    def forcenext(trees: XML.Body): XML.Body =
      trees match {
        case Nil => Nil
        case FBreak :: _ => trees
        case Break(_) :: ts => FBreak :: ts
        case t :: ts => t :: forcenext(ts)
      }

    def format(trees: XML.Body, blockin: Double, after: Double, text: Text): Text =
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
          else format(ts, blockin, after, text.newline.blanks(blockin.toInt))
        case FBreak :: ts => format(ts, blockin, after, text.newline.blanks(blockin.toInt))

        case XML.Elem(markup, body) :: ts =>
          val btext = format(body, blockin, breakdist(ts, after), text.copy(tx = Nil))
          val ts1 = if (text.nl < btext.nl) forcenext(ts) else ts
          val btext1 = btext.copy(tx = XML.Elem(markup, btext.content) :: text.tx)
          format(ts1, blockin, after, btext1)
        case XML.Text(s) :: ts => format(ts, blockin, after, text.string(s, metric(s)))
      }
    format(input.flatMap(standard_format), 0.0, 0.0, Text()).content
  }

  def string_of(input: XML.Body, margin: Int = margin_default,
      metric: String => Double = metric_default): String =
    formatted(input, margin, metric).iterator.flatMap(XML.content).mkString


  /* unformatted output */

  def unformatted(input: XML.Body): XML.Body =
  {
    def fmt(tree: XML.Tree): XML.Body =
      tree match {
        case Block(_, body) => body.flatMap(fmt)
        case Break(wd) => List(XML.Text(Symbol.spaces(wd)))
        case FBreak => List(XML.Text(Symbol.space))
        case XML.Elem(markup, body) => List(XML.Elem(markup, body.flatMap(fmt)))
        case XML.Text(_) => List(tree)
      }
    input.flatMap(standard_format).flatMap(fmt)
  }

  def str_of(input: XML.Body): String =
    unformatted(input).iterator.flatMap(XML.content).mkString
}
