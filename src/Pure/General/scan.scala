/*  Title:      Pure/General/scan.scala
    Author:     Makarius

Efficient scanning of keywords and tokens.
*/

package isabelle


import scala.collection.{IndexedSeq, TraversableOnce}
import scala.collection.immutable.PagedSeq
import scala.util.parsing.input.{OffsetPosition, Position => InputPosition, Reader}
import scala.util.parsing.combinator.RegexParsers

import java.io.{File => JFile, BufferedInputStream, FileInputStream}


object Scan
{
  /** context of partial scans **/

  sealed abstract class Context
  case object Finished extends Context
  case class Quoted(quote: String) extends Context
  case object Verbatim extends Context
  case class Cartouche(depth: Int) extends Context
  case class Comment(depth: Int) extends Context



  /** parser combinators **/

  object Parsers extends Parsers

  trait Parsers extends RegexParsers
  {
    override val whiteSpace = "".r


    /* optional termination */

    def opt_term[T](p: => Parser[T]): Parser[Option[T]] =
      p ^^ (x => Some(x)) | """\z""".r ^^ (_ => None)


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
          while (!finished && i < end && count < max_count) {
            val n = matcher(i, end)
            val sym = in.source.subSequence(i, i + n).toString
            if (pred(sym)) { i += n; count += 1 }
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

    def recover_quoted(quote: Symbol.Symbol): Parser[String] =
      quote ~ quoted_body(quote) ^^ { case x ~ y => x + y }


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

    val recover_verbatim: Parser[String] =
      "{*" ~ verbatim_body ^^ { case x ~ y => x + y }


    /* nested text cartouches */

    private def cartouche_depth(depth: Int): Parser[(String, Int)] = new Parser[(String, Int)]
    {
      require(depth >= 0)

      def apply(in: Input) =
      {
        val start = in.offset
        val end = in.source.length
        val matcher = new Symbol.Matcher(in.source)

        var i = start
        var d = depth
        var finished = false
        while (!finished && i < end) {
          val n = matcher(i, end)
          val sym = in.source.subSequence(i, i + n).toString
          if (Symbol.is_open(sym)) { i += n; d += 1 }
          else if (d > 0) { i += n; if (Symbol.is_close(sym)) d -= 1 }
          else finished = true
        }
        if (i == start) Failure("bad input", in)
        else Success((in.source.subSequence(start, i).toString, d), in.drop(i - start))
      }
    }.named("cartouche_depth")

    def cartouche: Parser[String] =
      cartouche_depth(0) ^? { case (x, d) if d == 0 => x }

    def cartouche_context(ctxt: Context): Parser[(String, Context)] =
    {
      val depth =
        ctxt match {
          case Finished => 0
          case Cartouche(d) => d
          case _ => -1
        }
      if (depth >= 0)
        cartouche_depth(depth) ^^
          { case (x, 0) => (x, Finished)
            case (x, d) => (x, Cartouche(d)) }
      else failure("")
    }

    val recover_cartouche: Parser[String] =
      cartouche_depth(0) ^^ (_._1)

    def cartouche_content(source: String): String =
    {
      def err(): Nothing = error("Malformed text cartouche: " + quote(source))
      val source1 =
        Library.try_unprefix(Symbol.open_decoded, source) orElse
          Library.try_unprefix(Symbol.open, source) getOrElse err()
      Library.try_unsuffix(Symbol.close_decoded, source1) orElse
        Library.try_unsuffix(Symbol.close, source1) getOrElse err()
    }


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

    val recover_comment: Parser[String] =
      comment_depth(0) ^^ (_._1)

    def comment_content(source: String): String =
    {
      require(parseAll(comment, source).successful)
      source.substring(2, source.length - 2)
    }


    /* keyword */

    def keyword(lexicon: Lexicon): Parser[String] = new Parser[String]
    {
      def apply(in: Input) =
      {
        val result = lexicon.scan(in)
        if (result.isEmpty) Failure("keyword expected", in)
        else Success(result, in.drop(result.length))
      }
    }.named("keyword")


    /* outer syntax tokens */

    private def delimited_token: Parser[Token] =
    {
      val string = quoted("\"") ^^ (x => Token(Token.Kind.STRING, x))
      val alt_string = quoted("`") ^^ (x => Token(Token.Kind.ALT_STRING, x))
      val verb = verbatim ^^ (x => Token(Token.Kind.VERBATIM, x))
      val cart = cartouche ^^ (x => Token(Token.Kind.CARTOUCHE, x))
      val cmt = comment ^^ (x => Token(Token.Kind.COMMENT, x))

      string | (alt_string | (verb | (cart | cmt)))
    }

    private def other_token(lexicon: Lexicon, is_command: String => Boolean)
      : Parser[Token] =
    {
      val letdigs1 = many1(Symbol.is_letdig)
      val sub = one(s => s == Symbol.sub_decoded || s == "\\<^sub>")
      val id =
        one(Symbol.is_letter) ~
          (rep(letdigs1 | (sub ~ letdigs1 ^^ { case x ~ y => x + y })) ^^ (_.mkString)) ^^
        { case x ~ y => x + y }

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

      val command_keyword =
        keyword(lexicon) ^^
          (x => Token(if (is_command(x)) Token.Kind.COMMAND else Token.Kind.KEYWORD, x))

      val space = many1(Symbol.is_blank) ^^ (x => Token(Token.Kind.SPACE, x))

      val recover_delimited =
        (recover_quoted("\"") |
          (recover_quoted("`") |
            (recover_verbatim |
              (recover_cartouche | recover_comment)))) ^^ (x => Token(Token.Kind.ERROR, x))

      val bad = one(_ => true) ^^ (x => Token(Token.Kind.ERROR, x))

      space | (recover_delimited |
        (((ident | (var_ | (type_ident | (type_var | (float | (nat_ | sym_ident)))))) |||
          command_keyword) | bad))
    }

    def token(lexicon: Lexicon, is_command: String => Boolean): Parser[Token] =
      delimited_token | other_token(lexicon, is_command)

    def token_context(lexicon: Lexicon, is_command: String => Boolean, ctxt: Context)
      : Parser[(Token, Context)] =
    {
      val string =
        quoted_context("\"", ctxt) ^^ { case (x, c) => (Token(Token.Kind.STRING, x), c) }
      val alt_string =
        quoted_context("`", ctxt) ^^ { case (x, c) => (Token(Token.Kind.ALT_STRING, x), c) }
      val verb = verbatim_context(ctxt) ^^ { case (x, c) => (Token(Token.Kind.VERBATIM, x), c) }
      val cart = cartouche_context(ctxt) ^^ { case (x, c) => (Token(Token.Kind.CARTOUCHE, x), c) }
      val cmt = comment_context(ctxt) ^^ { case (x, c) => (Token(Token.Kind.COMMENT, x), c) }
      val other = other_token(lexicon, is_command) ^^ { case x => (x, Finished) }

      string | (alt_string | (verb | (cart | (cmt | other))))
    }
  }



  /** Lexicon -- position tree **/

  object Lexicon
  {
    /* representation */

    private sealed case class Tree(val branches: Map[Char, (String, Tree)])
    private val empty_tree = Tree(Map())

    val empty: Lexicon = new Lexicon(empty_tree)
    def apply(elems: String*): Lexicon = empty ++ elems
  }

  final class Lexicon private(rep: Lexicon.Tree)
  {
    /* auxiliary operations */

    private def content(tree: Lexicon.Tree, result: List[String]): List[String] =
      (result /: tree.branches.toList) ((res, entry) =>
        entry match { case (_, (s, tr)) =>
          if (s.isEmpty) content(tr, res) else content(tr, s :: res) })

    private def lookup(str: CharSequence): Option[(Boolean, Lexicon.Tree)] =
    {
      val len = str.length
      def look(tree: Lexicon.Tree, tip: Boolean, i: Int): Option[(Boolean, Lexicon.Tree)] =
      {
        if (i < len) {
          tree.branches.get(str.charAt(i)) match {
            case Some((s, tr)) => look(tr, !s.isEmpty, i + 1)
            case None => None
          }
        } else Some(tip, tree)
      }
      look(rep, false, 0)
    }

    def completions(str: CharSequence): List[String] =
      lookup(str) match {
        case Some((true, tree)) => content(tree, List(str.toString))
        case Some((false, tree)) => content(tree, Nil)
        case None => Nil
      }


    /* pseudo Set methods */

    def iterator: Iterator[String] = content(rep, Nil).sorted.iterator

    override def toString: String = iterator.mkString("Lexicon(", ", ", ")")

    def empty: Lexicon = Lexicon.empty
    def isEmpty: Boolean = rep.branches.isEmpty

    def contains(elem: String): Boolean =
      lookup(elem) match {
        case Some((tip, _)) => tip
        case _ => false
      }


    /* add elements */

    def + (elem: String): Lexicon =
      if (contains(elem)) this
      else {
        val len = elem.length
        def extend(tree: Lexicon.Tree, i: Int): Lexicon.Tree =
          if (i < len) {
            val c = elem.charAt(i)
            val end = (i + 1 == len)
            tree.branches.get(c) match {
              case Some((s, tr)) =>
                Lexicon.Tree(tree.branches +
                  (c -> (if (end) elem else s, extend(tr, i + 1))))
              case None =>
                Lexicon.Tree(tree.branches +
                  (c -> (if (end) elem else "", extend(Lexicon.empty_tree, i + 1))))
            }
          }
          else tree
        new Lexicon(extend(rep, 0))
      }

    def ++ (elems: TraversableOnce[String]): Lexicon = (this /: elems)(_ + _)


    /* scan */

    def scan(in: Reader[Char]): String =
    {
      val source = in.source
      val offset = in.offset
      val len = source.length - offset

      def scan_tree(tree: Lexicon.Tree, result: String, i: Int): String =
      {
        if (i < len) {
          tree.branches.get(source.charAt(offset + i)) match {
            case Some((s, tr)) => scan_tree(tr, if (s.isEmpty) result else s, i + 1)
            case None => result
          }
        }
        else result
      }
      scan_tree(rep, "", 0)
    }
  }
}
