/*  Title:      Pure/General/scan.scala
    Author:     Makarius

Efficient scanning of keywords and tokens.
*/

package isabelle


import scala.collection.generic.Addable
import scala.collection.IndexedSeq
import scala.collection.immutable.PagedSeq
import scala.util.parsing.input.{OffsetPosition, Position => InputPosition, Reader}
import scala.util.parsing.combinator.RegexParsers

import java.io.{File, InputStream, BufferedInputStream, FileInputStream}


object Scan
{
  /** context of partial scans **/

  sealed abstract class Context
  case object Finished extends Context
  case class Quoted(quote: String) extends Context
  case object Verbatim extends Context
  case class Comment(depth: Int) extends Context



  /** Lexicon -- position tree **/

  object Lexicon
  {
    /* representation */

    sealed case class Tree(val branches: Map[Char, (String, Tree)])
    private val empty_tree = Tree(Map())

    val empty: Lexicon = new Lexicon(empty_tree)
    def apply(elems: String*): Lexicon = empty ++ elems
  }

  class Lexicon private(private val main_tree: Lexicon.Tree)
    extends Addable[String, Lexicon] with RegexParsers
  {
    import Lexicon.Tree


    /* auxiliary operations */

    private def content(tree: Tree, result: List[String]): List[String] =
      (result /: tree.branches.toList) ((res, entry) =>
        entry match { case (_, (s, tr)) =>
          if (s.isEmpty) content(tr, res) else content(tr, s :: res) })

    private def lookup(str: CharSequence): Option[(Boolean, Tree)] =
    {
      val len = str.length
      def look(tree: Tree, tip: Boolean, i: Int): Option[(Boolean, Tree)] =
      {
        if (i < len) {
          tree.branches.get(str.charAt(i)) match {
            case Some((s, tr)) => look(tr, !s.isEmpty, i + 1)
            case None => None
          }
        } else Some(tip, tree)
      }
      look(main_tree, false, 0)
    }

    def completions(str: CharSequence): List[String] =
      lookup(str) match {
        case Some((true, tree)) => content(tree, List(str.toString))
        case Some((false, tree)) => content(tree, Nil)
        case None => Nil
      }


    /* pseudo Set methods */

    def iterator: Iterator[String] = content(main_tree, Nil).sorted.iterator

    override def toString: String = iterator.mkString("Lexicon(", ", ", ")")

    def empty: Lexicon = Lexicon.empty
    def isEmpty: Boolean = main_tree.branches.isEmpty

    def contains(elem: String): Boolean =
      lookup(elem) match {
        case Some((tip, _)) => tip
        case _ => false
      }


    /* Addable methods */

    def repr = this

    def + (elem: String): Lexicon =
      if (contains(elem)) this
      else {
        val len = elem.length
        def extend(tree: Tree, i: Int): Tree =
          if (i < len) {
            val c = elem.charAt(i)
            val end = (i + 1 == len)
            tree.branches.get(c) match {
              case Some((s, tr)) =>
                Tree(tree.branches +
                  (c -> (if (end) elem else s, extend(tr, i + 1))))
              case None =>
                Tree(tree.branches +
                  (c -> (if (end) elem else "", extend(Lexicon.empty_tree, i + 1))))
            }
          }
          else tree
        val old = this
        new Lexicon(extend(old.main_tree, 0))
      }



    /** RegexParsers methods **/

    override val whiteSpace = "".r


    /* optional termination */

    def opt_term[T](p: => Parser[T]): Parser[Option[T]] =
      p ^^ (x => Some(x)) | """\z""".r ^^ (_ => None)


    /* keywords from lexicon */

    def keyword: Parser[String] = new Parser[String]
    {
      def apply(in: Input) =
      {
        val source = in.source
        val offset = in.offset
        val len = source.length - offset

        def scan(tree: Tree, result: String, i: Int): String =
        {
          if (i < len) {
            tree.branches.get(source.charAt(offset + i)) match {
              case Some((s, tr)) => scan(tr, if (s.isEmpty) result else s, i + 1)
              case None => result
            }
          }
          else result
        }
        val result = scan(main_tree, "", 0)
        if (result.isEmpty) Failure("keyword expected", in)
        else Success(result, in.drop(result.length))
      }
    }.named("keyword")


    /* symbol range */

    def symbol_range(pred: Symbol.Symbol => Boolean, min_count: Int, max_count: Int): Parser[String] =
      new Parser[String]
      {
        def apply(in: Input) =
        {
          val start = in.offset
          val end = in.source.length
          val matcher = new Symbol.Matcher(in.source)

          var i = start
          var count = 0
          var finished = false
          while (!finished) {
            if (i < end && count < max_count) {
              val n = matcher(i, end)
              val sym = in.source.subSequence(i, i + n).toString
              if (pred(sym)) { i += n; count += 1 }
              else finished = true
            }
            else finished = true
          }
          if (count < min_count) Failure("bad input", in)
          else Success(in.source.subSequence(start, i).toString, in.drop(i - start))
        }
      }.named("symbol_range")

    def one(pred: Symbol.Symbol => Boolean): Parser[String] =
      symbol_range(pred, 1, 1)

    def many(pred: Symbol.Symbol => Boolean): Parser[String] =
      symbol_range(pred, 0, Integer.MAX_VALUE)

    def many1(pred: Symbol.Symbol => Boolean): Parser[String] =
      symbol_range(pred, 1, Integer.MAX_VALUE)


    /* quoted strings */

    private def quoted_body(quote: Symbol.Symbol): Parser[String] =
    {
      rep(many1(sym => sym != quote && sym != "\\") | "\\" + quote | "\\\\" |
        (("""\\\d\d\d""".r) ^? { case x if x.substring(1, 4).toInt <= 255 => x })) ^^ (_.mkString)
    }

    private def quoted(quote: Symbol.Symbol): Parser[String] =
    {
      quote ~ quoted_body(quote) ~ quote ^^ { case x ~ y ~ z => x + y + z }
    }.named("quoted")

    def quoted_content(quote: Symbol.Symbol, source: String): String =
    {
      require(parseAll(quoted(quote), source).successful)
      val body = source.substring(1, source.length - 1)
      if (body.exists(_ == '\\')) {
        val content =
          rep(many1(sym => sym != quote && sym != "\\") |
              "\\" ~> (quote | "\\" | """\d\d\d""".r ^^ { case x => x.toInt.toChar.toString }))
        parseAll(content ^^ (_.mkString), body).get
      }
      else body
    }

    def quoted_context(quote: Symbol.Symbol, ctxt: Context): Parser[(String, Context)] =
    {
      ctxt match {
        case Finished =>
          quote ~ quoted_body(quote) ~ opt_term(quote) ^^
            { case x ~ y ~ Some(z) => (x + y + z, Finished)
              case x ~ y ~ None => (x + y, Quoted(quote)) }
        case Quoted(q) if q == quote =>
          quoted_body(quote) ~ opt_term(quote) ^^
            { case x ~ Some(y) => (x + y, Finished)
              case x ~ None => (x, ctxt) }
        case _ => failure("")
      }
    }.named("quoted_context")


    /* verbatim text */

    private def verbatim_body: Parser[String] =
      rep(many1(sym => sym != "*") | """\*(?!\})""".r) ^^ (_.mkString)

    private def verbatim: Parser[String] =
    {
      "{*" ~ verbatim_body ~ "*}" ^^ { case x ~ y ~ z => x + y + z }
    }.named("verbatim")

    def verbatim_content(source: String): String =
    {
      require(parseAll(verbatim, source).successful)
      source.substring(2, source.length - 2)
    }

    def verbatim_context(ctxt: Context): Parser[(String, Context)] =
    {
      ctxt match {
        case Finished =>
          "{*" ~ verbatim_body ~ opt_term("*}") ^^
            { case x ~ y ~ Some(z) => (x + y + z, Finished)
              case x ~ y ~ None => (x + y, Verbatim) }
        case Verbatim =>
          verbatim_body ~ opt_term("*}") ^^
            { case x ~ Some(y) => (x + y, Finished)
              case x ~ None => (x, Verbatim) }
        case _ => failure("")
      }
    }.named("verbatim_context")


    /* nested comments */

    private def comment_depth(depth: Int): Parser[(String, Int)] = new Parser[(String, Int)]
    {
      require(depth >= 0)

      val comment_text =
        rep1(many1(sym => sym != "*" && sym != "(") | """\*(?!\))|\((?!\*)""".r)

      def apply(in: Input) =
      {
        var rest = in
        def try_parse[A](p: Parser[A]): Boolean =
        {
          parse(p ^^^ (), rest) match {
            case Success(_, next) => { rest = next; true }
            case _ => false
          }
        }
        var d = depth
        var finished = false
        while (!finished) {
          if (try_parse("(*")) d += 1
          else if (d > 0 && try_parse("*)")) d -= 1
          else if (d == 0 || !try_parse(comment_text)) finished = true
        }
        if (in.offset < rest.offset)
          Success((in.source.subSequence(in.offset, rest.offset).toString, d), rest)
        else Failure("comment expected", in)
      }
    }.named("comment_depth")

    def comment: Parser[String] =
      comment_depth(0) ^? { case (x, d) if d == 0 => x }

    def comment_context(ctxt: Context): Parser[(String, Context)] =
    {
      val depth =
        ctxt match {
          case Finished => 0
          case Comment(d) => d
          case _ => -1
        }
      if (depth >= 0)
        comment_depth(depth) ^^
          { case (x, 0) => (x, Finished)
            case (x, d) => (x, Comment(d)) }
      else failure("")
    }

    def comment_content(source: String): String =
    {
      require(parseAll(comment, source).successful)
      source.substring(2, source.length - 2)
    }


    /* outer syntax tokens */

    private def delimited_token: Parser[Token] =
    {
      val string = quoted("\"") ^^ (x => Token(Token.Kind.STRING, x))
      val alt_string = quoted("`") ^^ (x => Token(Token.Kind.ALT_STRING, x))
      val verb = verbatim ^^ (x => Token(Token.Kind.VERBATIM, x))
      val cmt = comment ^^ (x => Token(Token.Kind.COMMENT, x))

      string | (alt_string | (verb | cmt))
    }

    private def other_token(is_command: String => Boolean)
      : Parser[Token] =
    {
      val id = one(Symbol.is_letter) ~ many(Symbol.is_letdig) ^^ { case x ~ y => x + y }
      val nat = many1(Symbol.is_digit)
      val natdot = nat ~ "." ~ nat ^^ { case x ~ y ~ z => x + y + z }
      val id_nat = id ~ opt("." ~ nat) ^^ { case x ~ Some(y ~ z) => x + y + z case x ~ None => x }

      val ident = id ~ rep("." ~> id) ^^
        { case x ~ Nil => Token(Token.Kind.IDENT, x)
          case x ~ ys => Token(Token.Kind.LONG_IDENT, (x :: ys).mkString(".")) }

      val var_ = "?" ~ id_nat ^^ { case x ~ y => Token(Token.Kind.VAR, x + y) }
      val type_ident = "'" ~ id ^^ { case x ~ y => Token(Token.Kind.TYPE_IDENT, x + y) }
      val type_var = "?'" ~ id_nat ^^ { case x ~ y => Token(Token.Kind.TYPE_VAR, x + y) }
      val nat_ = nat ^^ (x => Token(Token.Kind.NAT, x))
      val float =
        ("-" ~ natdot ^^ { case x ~ y => x + y } | natdot) ^^ (x => Token(Token.Kind.FLOAT, x))

      val sym_ident =
        (many1(Symbol.is_symbolic_char) | one(sym => Symbol.is_symbolic(sym))) ^^
        (x => Token(Token.Kind.SYM_IDENT, x))

      val space = many1(Symbol.is_blank) ^^ (x => Token(Token.Kind.SPACE, x))

      // FIXME check
      val junk = many(sym => !(Symbol.is_blank(sym)))
      val junk1 = many1(sym => !(Symbol.is_blank(sym)))

      val bad_delimiter =
        ("\"" | "`" | "{*" | "(*") ~ junk ^^ { case x ~ y => Token(Token.Kind.UNPARSED, x + y) }
      val bad = junk1 ^^ (x => Token(Token.Kind.UNPARSED, x))

      val command_keyword =
        keyword ^^ (x => Token(if (is_command(x)) Token.Kind.COMMAND else Token.Kind.KEYWORD, x))

      space | (bad_delimiter |
        (((ident | (var_ | (type_ident | (type_var | (float | (nat_ | sym_ident)))))) |||
          command_keyword) | bad))
    }

    def token(is_command: String => Boolean): Parser[Token] =
      delimited_token | other_token(is_command)

    def token_context(is_command: String => Boolean, ctxt: Context): Parser[(Token, Context)] =
    {
      val string =
        quoted_context("\"", ctxt) ^^ { case (x, c) => (Token(Token.Kind.STRING, x), c) }
      val alt_string =
        quoted_context("`", ctxt) ^^ { case (x, c) => (Token(Token.Kind.ALT_STRING, x), c) }
      val verb = verbatim_context(ctxt) ^^ { case (x, c) => (Token(Token.Kind.VERBATIM, x), c) }
      val cmt = comment_context(ctxt) ^^ { case (x, c) => (Token(Token.Kind.COMMENT, x), c) }
      val other = other_token(is_command) ^^ { case x => (x, Finished) }

      string | (alt_string | (verb | (cmt | other)))
    }
  }



  /** read file without decoding -- enables efficient length operation **/

  private class Restricted_Seq(seq: IndexedSeq[Char], start: Int, end: Int)
    extends CharSequence
  {
    def charAt(i: Int): Char =
      if (0 <= i && i < length) seq(start + i)
      else throw new IndexOutOfBoundsException

    def length: Int = end - start  // avoid potentially expensive seq.length

    def subSequence(i: Int, j: Int): CharSequence =
      if (0 <= i && i <= j && j <= length) new Restricted_Seq(seq, start + i, start + j)
      else throw new IndexOutOfBoundsException

    override def toString: String =
    {
      val buf = new StringBuilder(length)
      for (offset <- start until end) buf.append(seq(offset))
      buf.toString
    }
  }

  abstract class Byte_Reader extends Reader[Char] { def close: Unit }

  def byte_reader(file: File): Byte_Reader =
  {
    val stream = new BufferedInputStream(new FileInputStream(file))
    val seq = new PagedSeq(
      (buf: Array[Char], offset: Int, length: Int) =>
        {
          var i = 0
          var c = 0
          var eof = false
          while (!eof && i < length) {
            c = stream.read
            if (c == -1) eof = true
            else { buf(offset + i) = c.toChar; i += 1 }
          }
          if (i > 0) i else -1
        })
    val restricted_seq = new Restricted_Seq(seq, 0, file.length.toInt)

    class Paged_Reader(override val offset: Int) extends Byte_Reader
    {
      override lazy val source: CharSequence = restricted_seq
      def first: Char = if (seq.isDefinedAt(offset)) seq(offset) else '\032'
      def rest: Paged_Reader = if (seq.isDefinedAt(offset)) new Paged_Reader(offset + 1) else this
      def pos: InputPosition = new OffsetPosition(source, offset)
      def atEnd: Boolean = !seq.isDefinedAt(offset)
      override def drop(n: Int): Paged_Reader = new Paged_Reader(offset + n)
      def close { stream.close }
    }
    new Paged_Reader(0)
  }
}
