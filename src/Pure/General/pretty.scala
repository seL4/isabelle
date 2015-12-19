/*  Title:      Pure/General/pretty.scala
    Author:     Makarius

Generic pretty printing module.
*/

package isabelle


object Pretty
{
  /* spaces */

  def spaces(n: Int): XML.Body =
    if (n == 0) Nil
    else List(XML.Text(Symbol.spaces(n)))

  val space: XML.Body = spaces(1)


  /* text metric -- standardized to width of space */

  abstract class Metric
  {
    val unit: Double
    def apply(s: String): Double
    def content_length(body: XML.Body): Double =
      XML.traverse_text(body)(0.0)(_ + apply(_))
  }

  object Metric_Default extends Metric
  {
    val unit = 1.0
    def apply(s: String): Double = s.length.toDouble
  }


  /* markup trees with physical blocks and breaks */

  def block(body: XML.Body): XML.Tree = Block(false, 2, body)

  object Block
  {
    def apply(consistent: Boolean, indent: Int, body: XML.Body): XML.Tree =
      XML.Elem(Markup.Block(consistent, indent), body)

    def unapply(tree: XML.Tree): Option[(Boolean, Int, XML.Body)] =
      tree match {
        case XML.Elem(Markup.Block(consistent, indent), body) => Some((consistent, indent, body))
        case _ => None
      }
  }

  object Break
  {
    def apply(w: Int, i: Int = 0): XML.Tree =
      XML.Elem(Markup.Break(w, i), spaces(w))

    def unapply(tree: XML.Tree): Option[(Int, Int)] =
      tree match {
        case XML.Elem(Markup.Break(w, i), _) => Some((w, i))
        case _ => None
      }
  }

  val FBreak = XML.Text("\n")

  def item(body: XML.Body): XML.Tree =
    Block(false, 2, XML.elem(Markup.BULLET, space) :: space ::: body)

  val Separator = List(XML.elem(Markup.SEPARATOR, space), FBreak)
  def separate(ts: List[XML.Tree]): XML.Body = Library.separate(Separator, ts.map(List(_))).flatten


  /* standard form */

  def standard_form(body: XML.Body): XML.Body =
    body flatMap {
      case XML.Wrapped_Elem(markup, body1, body2) =>
        List(XML.Wrapped_Elem(markup, body1, standard_form(body2)))
      case XML.Elem(markup, body) =>
        if (markup.name == Markup.ITEM) List(item(standard_form(body)))
        else List(XML.Elem(markup, standard_form(body)))
      case XML.Text(text) => Library.separate(FBreak, split_lines(text).map(XML.Text))
    }


  /* formatted output */

  private val margin_default = 76.0

  def formatted(input: XML.Body, margin: Double = margin_default,
    metric: Metric = Metric_Default): XML.Body =
  {
    sealed case class Text(tx: XML.Body = Nil, pos: Double = 0.0, nl: Int = 0)
    {
      def newline: Text = copy(tx = FBreak :: tx, pos = 0.0, nl = nl + 1)
      def string(s: String): Text =
        if (s == "") this
        else copy(tx = XML.Text(s) :: tx, pos = pos + metric(s))
      def blanks(wd: Int): Text = string(Symbol.spaces(wd))
      def content: XML.Body = tx.reverse
    }

    val breakgain = margin / 20
    val emergencypos = (margin / 2).round.toInt

    def break_dist(trees: XML.Body, after: Double): Double =
      trees match {
        case Break(_, _) :: _ => 0.0
        case FBreak :: _ => 0.0
        case t :: ts => metric.content_length(List(t)) + break_dist(ts, after)
        case Nil => after
      }

    def force_all(trees: XML.Body): XML.Body =
      trees flatMap {
        case Break(_, ind) => FBreak :: spaces(ind)
        case tree => List(tree)
      }

    def force_next(trees: XML.Body): XML.Body =
      trees match {
        case Nil => Nil
        case FBreak :: _ => trees
        case Break(_, ind) :: ts => FBreak :: spaces(ind) ::: ts
        case t :: ts => t :: force_next(ts)
      }

    def format(trees: XML.Body, blockin: Int, after: Double, text: Text): Text =
      trees match {
        case Nil => text

        case Block(consistent, indent, body) :: ts =>
          val pos1 = (text.pos + indent).ceil.toInt
          val pos2 = pos1 % emergencypos
          val blockin1 = if (pos1 < emergencypos) pos1 else pos2
          val blen = metric.content_length(body)
          val d = break_dist(ts, after)
          val body1 = if (consistent && text.pos + blen > margin - d) force_all(body) else body
          val btext = format(body1, blockin1, d, text)
          val ts1 = if (text.nl < btext.nl) force_next(ts) else ts
          format(ts1, blockin, after, btext)

        case Break(wd, ind) :: ts =>
          if (text.pos + wd <= ((margin - break_dist(ts, after)) max (blockin + breakgain)))
            format(ts, blockin, after, text.blanks(wd))
          else format(ts, blockin, after, text.newline.blanks(blockin + ind))
        case FBreak :: ts => format(ts, blockin, after, text.newline.blanks(blockin))

        case XML.Wrapped_Elem(markup, body1, body2) :: ts =>
          val btext = format(body2, blockin, break_dist(ts, after), text.copy(tx = Nil))
          val ts1 = if (text.nl < btext.nl) force_next(ts) else ts
          val btext1 = btext.copy(tx = XML.Wrapped_Elem(markup, body1, btext.content) :: text.tx)
          format(ts1, blockin, after, btext1)

        case XML.Elem(markup, body) :: ts =>
          val btext = format(body, blockin, break_dist(ts, after), text.copy(tx = Nil))
          val ts1 = if (text.nl < btext.nl) force_next(ts) else ts
          val btext1 = btext.copy(tx = XML.Elem(markup, btext.content) :: text.tx)
          format(ts1, blockin, after, btext1)

        case XML.Text(s) :: ts => format(ts, blockin, after, text.string(s))
      }

    format(standard_form(input), 0, 0.0, Text()).content
  }

  def string_of(input: XML.Body, margin: Double = margin_default,
      metric: Metric = Metric_Default): String =
    XML.content(formatted(input, margin, metric))


  /* unformatted output */

  def unformatted(input: XML.Body): XML.Body =
  {
    def fmt(tree: XML.Tree): XML.Body =
      tree match {
        case Block(_, _, body) => body.flatMap(fmt)
        case Break(wd, _) => spaces(wd)
        case FBreak => space
        case XML.Wrapped_Elem(markup, body1, body2) =>
          List(XML.Wrapped_Elem(markup, body1, body2.flatMap(fmt)))
        case XML.Elem(markup, body) => List(XML.Elem(markup, body.flatMap(fmt)))
        case XML.Text(_) => List(tree)
      }
    standard_form(input).flatMap(fmt)
  }

  def str_of(input: XML.Body): String = XML.content(unformatted(input))
}
