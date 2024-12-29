/*  Title:      Pure/General/pretty.scala
    Author:     Makarius

Generic pretty printing module.
*/

package isabelle

import scala.annotation.tailrec


object Pretty {
  /* XML constructors */

  val space: XML.Body = List(XML.Text(Symbol.space))
  def spaces(n: Int): XML.Body =
    if (n == 0) Nil
    else if (n == 1) space
    else List(XML.Text(Symbol.spaces(n)))

  val bullet: XML.Body = XML.elem(Markup.BULLET, space) :: space

  def block(body: XML.Body,
    consistent: Boolean = false,
    indent: Int = 2
  ): XML.Elem = XML.Elem(Markup.Block(consistent = consistent, indent = indent), body)

  def string(s: String): XML.Elem = block(XML.string(s), indent = 0)

  def brk(width: Int, indent: Int = 0): XML.Elem =
    XML.Elem(Markup.Break(width = width, indent = indent), spaces(width))

  val fbrk: XML.Tree = XML.newline
  def fbreaks(ts: List[XML.Tree]): XML.Body = Library.separate(fbrk, ts)

  val Separator: XML.Body = List(XML.elem(Markup.SEPARATOR, space), fbrk)
  def separate(ts: List[XML.Tree], sep: XML.Body = Separator): XML.Body =
    Library.separate(sep, ts.map(List(_))).flatten

  val comma: XML.Body = List(XML.Text(","), brk(1))
  def commas(ts: List[XML.Tree]): XML.Body = separate(ts, sep = comma)

  def `enum`(ts: List[XML.Tree],
    bg: String = "(",
    en: String = ")",
    sep: XML.Body = comma,
    indent: Int = 2
  ): XML.Elem = Pretty.block(XML.enclose(bg, en, separate(ts, sep = sep)), indent = indent)


  /* text metric -- standardized to width of space */

  abstract class Metric {
    def unit: Double
    def apply(s: String): Double
  }


  /* markup trees with physical blocks and breaks */

  private def force_nat(i: Int): Int = i max 0

  private sealed abstract class Tree { def length: Double }
  private case class Block(
    markup: Markup,
    markup_body: Option[XML.Body],
    open_block: Boolean,
    consistent: Boolean,
    indent: Int,
    body: List[Tree],
    length: Double
  ) extends Tree {
    def no_markup: Boolean = markup.is_empty && markup_body.isEmpty
    def markup_elem(body: XML.Body): XML.Elem =
      if (markup_body.isEmpty) XML.Elem(markup, body)
      else XML.Wrapped_Elem(markup, markup_body.get, body)
  }
  private case class Break(force: Boolean, width: Int, indent: Int) extends Tree {
    def length: Double = width.toDouble
  }
  private case class Str(string: String, length: Double) extends Tree

  private val FBreak = Break(true, 1, 0)

  private def make_block(body: List[Tree],
    markup: Markup = Markup.Empty,
    markup_body: Option[XML.Body] = None,
    open_block: Boolean = false,
    consistent: Boolean = false,
    indent: Int = 0
  ): Tree = {
    val indent1 = force_nat(indent)

    @tailrec def body_length(prts: List[Tree], len: Double): Double = {
      val (line, rest) =
        Library.take_prefix[Tree]({ case Break(true, _, _) => false case _ => true }, prts)
      val len1 = (line.foldLeft(0.0) { case (l, t) => l + t.length }) max len
      (rest: @unchecked) match {
        case Break(true, _, ind) :: rest1 =>
          body_length(Break(false, indent1 + ind, 0) :: rest1, len1)
        case Nil => len1
      }
    }
    Block(markup, markup_body, open_block, consistent, indent1, body, body_length(body, 0.0))
  }


  /* no formatting */

  def output_content(pure: Boolean, output: XML.Body): String =
    XML.content(if (pure) Protocol_Message.clean_output(output) else output)

  def unbreakable(input: XML.Body): XML.Body =
    input flatMap {
      case XML.Wrapped_Elem(markup, body1, body2) =>
        List(XML.Wrapped_Elem(markup, body1, unbreakable(body2)))
      case XML.Elem(Markup.Break(width, _), _) => spaces(width)
      case XML.Elem(markup, body) => List(XML.Elem(markup, unbreakable(body)))
      case XML.Text(text) => XML.string(split_lines(text).mkString(Symbol.space))
    }

  def unformatted_string_of(input: XML.Body, pure: Boolean = false): String =
    output_content(pure, unbreakable(input))


  /* formatting */

  private sealed case class Text(tx: XML.Body = Nil, pos: Double = 0.0, nl: Int = 0) {
    def set(body: XML.Body): Text = copy(tx = body)
    def reset: Text = if (tx.isEmpty) this else copy(tx = Nil)
    def content: XML.Body = tx.reverse

    def newline: Text = copy(tx = fbrk :: tx, pos = 0.0, nl = nl + 1)
    def string(s: String, len: Double): Text =
      copy(tx = if (s == "") tx else XML.Text(s) :: tx, pos = pos + len)
    def blanks(wd: Int): Text = string(Symbol.spaces(wd), wd.toDouble)
  }

  private def break_dist(trees: List[Tree], after: Double): Double =
    trees match {
      case (_: Break) :: _ => 0.0
      case t :: ts => t.length + break_dist(ts, after)
      case Nil => after
    }

  private def force_break(tree: Tree): Tree =
    tree match { case Break(false, wd, ind) => Break(true, wd, ind) case _ => tree }
  private def force_all(trees: List[Tree]): List[Tree] = trees.map(force_break)

  private def force_next(trees: List[Tree]): List[Tree] =
    trees match {
      case Nil => Nil
      case (t: Break) :: ts => force_break(t) :: ts
      case t :: ts => t :: force_next(ts)
    }

  val default_margin: Double = 76.0
  val default_breakgain: Double = default_margin / 20

  def formatted(input: XML.Body,
    margin: Double = default_margin,
    breakgain: Double = default_breakgain,
    metric: Metric = Codepoint.Metric
  ): XML.Body = {
    val emergencypos = (margin / 2).round.toInt

    def make_tree(inp: XML.Body): List[Tree] =
      inp flatMap {
        case XML.Wrapped_Elem(markup, markup_body, body) =>
          List(make_block(make_tree(body),
            markup = markup, markup_body = Some(markup_body), open_block = true))
        case XML.Elem(markup, body) =>
          markup match {
            case Markup.Block(consistent, indent) =>
              List(make_block(make_tree(body), consistent = consistent, indent = indent))
            case Markup.Break(width, indent) =>
              List(Break(false, force_nat(width), force_nat(indent)))
            case Markup(Markup.ITEM, _) =>
              val item = make_tree(bullet ::: body)
              List(make_block(item, markup = Markup.Expression.item, indent = 2))
            case _ =>
              List(make_block(make_tree(body), markup = markup, open_block = true))
          }
        case XML.Text(text) =>
          Library.separate(FBreak, split_lines(text).map(s => Str(s, metric(s))))
      }

    def format(trees: List[Tree], blockin: Int, after: Double, text: Text): Text =
      trees match {
        case Nil => text

        case (block: Block) :: ts if block.open_block =>
          val btext = format(block.body, blockin, break_dist(ts, after), text.reset)
          val elem = block.markup_elem(btext.content)
          val btext1 = btext.set(elem :: text.tx)
          val ts1 = if (text.nl < btext1.nl) force_next(ts) else ts
          format(ts1, blockin, after, btext1)

        case (block: Block) :: ts =>
          val pos1 = (text.pos + block.indent).ceil.toInt
          val pos2 = pos1 % emergencypos
          val blockin1 = if (pos1 < emergencypos) pos1 else pos2
          val after1 = break_dist(ts, after)
          val body1 =
            if (block.consistent && text.pos + block.length > margin - after1) force_all(block.body)
            else block.body
          val btext1 =
            if (block.no_markup) format(body1, blockin1, after1, text)
            else {
              val btext = format(body1, blockin1, after1, text.reset)
              val elem = block.markup_elem(btext.content)
              btext.set(elem :: text.tx)
            }
          val ts1 = if (text.nl < btext1.nl) force_next(ts) else ts
          format(ts1, blockin, after, btext1)

        case Break(force, wd, ind) :: ts =>
          if (!force &&
              text.pos + wd <= ((margin - break_dist(ts, after)) max (blockin + breakgain)))
            format(ts, blockin, after, text.blanks(wd))
          else format(ts, blockin, after, text.newline.blanks(blockin + ind))

        case Str(s, len) :: ts => format(ts, blockin, after, text.string(s, len))
      }
    format(make_tree(input), 0, 0.0, Text()).content
  }

  def string_of(input: XML.Body,
    margin: Double = default_margin,
    breakgain: Double = default_breakgain,
    metric: Metric = Codepoint.Metric,
    pure: Boolean = false
  ): String = {
    output_content(pure, formatted(input, margin = margin, breakgain = breakgain, metric = metric))
  }
}
