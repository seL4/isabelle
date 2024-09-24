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

  def block(body: XML.Body, consistent: Boolean = false, indent: Int = 2): XML.Tree =
    XML.Elem(Markup.Block(consistent, indent), body)

  def brk(width: Int, indent: Int = 0): XML.Tree =
    XML.Elem(Markup.Break(width, indent), spaces(width))

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
  ): XML.Tree = Pretty.block(XML.enclose(bg, en, separate(ts, sep = sep)), indent = indent)


  /* text metric -- standardized to width of space */

  abstract class Metric {
    val unit: Double
    def apply(s: String): Double
  }

  object Default_Metric extends Metric {
    val unit = 1.0
    def apply(s: String): Double = Codepoint.length(s).toDouble
  }


  /* markup trees with physical blocks and breaks */

  private def force_nat(i: Int): Int = i max 0

  private sealed abstract class Tree { def length: Double }
  private case class Block(
    markup: Markup,
    markup_body: Option[XML.Body],
    consistent: Boolean,
    indent: Int,
    body: List[Tree],
    length: Double
  ) extends Tree
  private case class Break(force: Boolean, width: Int, indent: Int) extends Tree {
    def length: Double = width.toDouble
  }
  private case class Str(string: String, length: Double) extends Tree

  private val FBreak = Break(true, 1, 0)

  private def make_block(body: List[Tree],
    markup: Markup = Markup.Empty,
    markup_body: Option[XML.Body] = None,
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
    Block(markup, markup_body, consistent, indent1, body, body_length(body, 0.0))
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
    def newline: Text = copy(tx = fbrk :: tx, pos = 0.0, nl = nl + 1)
    def string(s: String, len: Double): Text =
      copy(tx = if (s == "") tx else XML.Text(s) :: tx, pos = pos + len)
    def blanks(wd: Int): Text = string(Symbol.spaces(wd), wd.toDouble)
    def content: XML.Body = tx.reverse
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
    metric: Metric = Default_Metric
  ): XML.Body = {
    val emergencypos = (margin / 2).round.toInt

    def make_tree(inp: XML.Body): List[Tree] =
      inp flatMap {
        case XML.Wrapped_Elem(markup, body1, body2) =>
          List(make_block(make_tree(body2), markup = markup, markup_body = Some(body1)))
        case XML.Elem(markup, body) =>
          markup match {
            case Markup.Block(consistent, indent) =>
              List(make_block(make_tree(body), consistent = consistent, indent = indent))
            case Markup.Break(width, indent) =>
              List(Break(false, force_nat(width), force_nat(indent)))
            case Markup(Markup.ITEM, _) =>
              List(make_block(make_tree(bullet ::: body), indent = 2))
            case _ =>
              List(make_block(make_tree(body), markup = markup))
          }
        case XML.Text(text) =>
          Library.separate(FBreak, split_lines(text).map(s => Str(s, metric(s))))
      }

    def format(trees: List[Tree], blockin: Int, after: Double, text: Text): Text =
      trees match {
        case Nil => text

        case Block(markup, markup_body, consistent, indent, body, blen) :: ts =>
          val pos1 = (text.pos + indent).ceil.toInt
          val pos2 = pos1 % emergencypos
          val blockin1 = if (pos1 < emergencypos) pos1 else pos2
          val d = break_dist(ts, after)
          val body1 = if (consistent && text.pos + blen > margin - d) force_all(body) else body
          val btext =
            if (markup.is_empty && markup_body.isEmpty) format(body1, blockin1, d, text)
            else {
              val btext0 = format(body1, blockin1, d, text.copy(tx = Nil))
              val elem =
                markup_body match {
                  case None => XML.Elem(markup, btext0.content)
                  case Some(body1) => XML.Wrapped_Elem(markup, body1, btext0.content)
                }
              btext0.copy(tx = elem :: text.tx)
            }
          val ts1 = if (text.nl < btext.nl) force_next(ts) else ts
          format(ts1, blockin, after, btext)

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
    metric: Metric = Default_Metric,
    pure: Boolean = false
  ): String = {
    output_content(pure, formatted(input, margin = margin, breakgain = breakgain, metric = metric))
  }
}
