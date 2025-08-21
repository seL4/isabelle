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

  type Markup_Body = (Markup, Option[XML.Body])
  val no_markup: Markup_Body = (Markup.Empty, None)
  val item_markup: Markup_Body = (Markup.Expression.item, None)

  private sealed abstract class Tree { def length: Double }
  private case object End extends Tree {
    override def length: Double = 0.0
  }
  private case class Block(
    markup: Markup_Body,
    open_block: Boolean,
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
    markup: Markup_Body = no_markup,
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
    Block(markup, open_block, consistent, indent1, body, body_length(body, 0.0))
  }


  /* no formatting */

  def output_content(pure: Boolean, output: XML.Body): String =
    XML.content(if (pure) Protocol_Message.clean_output(output) else output)

  def unbreakable(input: XML.Body): XML.Body =
    input flatMap {
      case XML.Wrapped_Elem(markup1, markup2, body) =>
        List(XML.Wrapped_Elem(markup1, markup2, unbreakable(body)))
      case XML.Elem(Markup.Break(width, _), _) => spaces(width)
      case XML.Elem(markup, body) => List(XML.Elem(markup, unbreakable(body)))
      case XML.Text(text) => XML.string(split_lines(text).mkString(Symbol.space))
    }

  def unformatted_string_of(input: XML.Body, pure: Boolean = false): String =
    output_content(pure, unbreakable(input))


  /* formatting */

  private sealed abstract class Tree_Buffer { def result: XML.Tree }
  private case class Elem_Buffer(markup: Markup_Body, body: XML.Body) extends Tree_Buffer {
    def result: XML.Elem =
      markup match {
        case (m, None) => XML.Elem(m, body)
        case (m1, Some(m2)) => XML.Wrapped_Elem(m1, m2, body)
      }
  }
  private case class Text_Buffer(buffer: List[String]) extends Tree_Buffer {
    def result: XML.Text = XML.Text(buffer.reverse.mkString)

    def add(s: String): Text_Buffer =
      if (s.isEmpty) this else copy(buffer = s :: buffer)
  }

  private case class Result_Buffer(
    markup: Markup_Body = no_markup,
    buffer: List[Tree_Buffer] = Nil
  ) {
    def result_body: XML.Body = buffer.foldLeft[XML.Body](Nil)((res, t) => t.result :: res)
    def result_elem: Elem_Buffer = Elem_Buffer(markup, result_body)

    def add(elem: Elem_Buffer): Result_Buffer = copy(buffer = elem :: buffer)

    def string(s: String): Result_Buffer =
      if (s.isEmpty) this
      else {
        buffer match {
          case (text: Text_Buffer) :: ts => copy(buffer = text.add(s) :: ts)
          case _ => copy(buffer = Text_Buffer(List(s)) :: buffer)
        }
      }
  }

  private type State = List[Result_Buffer]
  private val init_state: State = List(Result_Buffer())

  private sealed case class Text(
    main: State = init_state,
    pos: Double = 0.0,
    nl: Int = 0
  ) {
    def add(elem: Elem_Buffer): Text =
      (main: @unchecked) match {
        case res :: rest => copy(main = res.add(elem) :: rest)
      }

    def push(m: Markup_Body): Text =
      copy(main = Result_Buffer(markup = m) :: main)

    def pop: Text =
      (main: @unchecked) match {
        case res1 :: res2 :: rest => copy(main = res2.add(res1.result_elem) :: rest)
      }

    def result: XML.Body =
      (main: @unchecked) match {
        case List(res) if res.markup == no_markup => res.result_body
      }

    def reset: Text = copy(main = init_state)
    def restore(other: Text): Text = copy(main = other.main)

    def string(s: String, len: Double): Text =
      (main: @unchecked) match {
        case res :: rest => copy(main = res.string(s) :: rest, pos = pos + len)
      }
    def blanks(wd: Int): Text = string(Symbol.spaces(wd), wd.toDouble)
    def newline: Text = string("\n", 0.0).copy(pos = 0.0, nl = nl + 1)
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
    recode: String => String = identity,
    margin: Double = default_margin,
    breakgain: Double = default_breakgain,
    metric: Metric = Codepoint.Metric
  ): XML.Body = {
    val margin_defined = margin > 0
    val margin1 = if (margin_defined) margin else default_margin
    val emergencypos = ((margin1 / 2) max 1).round.toInt

    def make_tree(inp: XML.Body): List[Tree] =
      inp flatMap {
        case XML.Wrapped_Elem(markup1, markup2, body) =>
          List(make_block(make_tree(body), markup = (markup1, Some(markup2)), open_block = true))
        case XML.Elem(markup, body) =>
          markup match {
            case Markup.Block(consistent, indent) =>
              List(make_block(make_tree(body), consistent = consistent, indent = indent))
            case Markup.Break(width, indent) =>
              List(Break(false, force_nat(width), force_nat(indent)))
            case Markup(Markup.ITEM, _) =>
              List(make_block(make_tree(bullet ::: body), markup = item_markup, indent = 2))
            case _ =>
              List(make_block(make_tree(body), markup = (markup, None), open_block = true))
          }
        case XML.Text(text) =>
          Library.separate(FBreak,
            split_lines(text).map { s0 => val s = recode(s0); Str(s, metric(s)) })
      }

    def format(trees: List[Tree], before: Double, after: Double, text: Text): Text =
      trees match {
        case Nil => text
        case End :: ts => format(ts, before, after, text.pop)
        case (block: Block) :: ts if block.open_block =>
          format(block.body ::: End :: ts, before, after, text.push(block.markup))
        case (block: Block) :: ts =>
          val pos1 = text.pos + block.indent
          val pos2 = (pos1.round.toInt % emergencypos).toDouble
          val before1 = if (!margin_defined || pos1 < emergencypos) pos1 else pos2
          val after1 = break_dist(ts, after)
          val body1 =
            if (margin_defined && block.consistent && text.pos + block.length > margin - after1) {
              force_all(block.body)
            }
            else block.body
          val btext1 =
            if (block.markup == no_markup) format(body1, before1, after1, text)
            else {
              val btext = format(body1, before1, after1, text.reset)
              val elem = Elem_Buffer(block.markup, btext.result)
              btext.restore(text.add(elem))
            }
          val ts1 = if (text.nl < btext1.nl) force_next(ts) else ts
          format(ts1, before, after, btext1)
        case Break(force, wd, ind) :: ts =>
          if (!force &&
              (!margin_defined ||
                text.pos + wd <= ((margin - break_dist(ts, after)) max (before + breakgain)))) {
            format(ts, before, after, text.blanks(wd))
          }
          else format(ts, before, after, text.newline.blanks((before + ind).ceil.toInt))
        case Str(s, len) :: ts => format(ts, before, after, text.string(s, len))
      }
    format(make_tree(input), 0.0, 0.0, Text()).result
  }

  def string_of(input: XML.Body,
    recode: String => String = identity,
    margin: Double = default_margin,
    breakgain: Double = default_breakgain,
    metric: Metric = Codepoint.Metric,
    pure: Boolean = false
  ): String = {
    val out =
      formatted(input, recode = recode, margin = margin, breakgain = breakgain, metric = metric)
    output_content(pure, out)
  }
}
