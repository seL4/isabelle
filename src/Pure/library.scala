/*  Title:      Pure/library.scala
    Author:     Makarius

Basic library.
*/

package isabelle


import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.matching.Regex


object Library
{
  /* resource management */

  def using[A <: AutoCloseable, B](a: A)(f: A => B): B =
  {
    try { f(a) }
    finally { if (a != null) a.close() }
  }


  /* integers */

  private val small_int = 10000
  private lazy val small_int_table =
  {
    val array = new Array[String](small_int)
    for (i <- 0 until small_int) array(i) = i.toString
    array
  }

  def is_small_int(s: String): Boolean =
  {
    val len = s.length
    1 <= len && len <= 4 &&
    s.forall(c => '0' <= c && c <= '9') &&
    (len == 1 || s(0) != '0')
  }

  def signed_string_of_long(i: Long): String =
    if (0 <= i && i < small_int) small_int_table(i.toInt)
    else i.toString

  def signed_string_of_int(i: Int): String =
    if (0 <= i && i < small_int) small_int_table(i)
    else i.toString


  /* separated chunks */

  def separate[A](s: A, list: List[A]): List[A] =
  {
    val result = new mutable.ListBuffer[A]
    var first = true
    for (x <- list) {
      if (first) {
        first = false
        result += x
      }
      else {
        result += s
        result += x
      }
    }
    result.toList
  }

  def separated_chunks(sep: Char => Boolean, source: CharSequence): Iterator[CharSequence] =
    new Iterator[CharSequence] {
      private val end = source.length
      private def next_chunk(i: Int): Option[(CharSequence, Int)] =
      {
        if (i < end) {
          var j = i; do j += 1 while (j < end && !sep(source.charAt(j)))
          Some((source.subSequence(i + 1, j), j))
        }
        else None
      }
      private var state: Option[(CharSequence, Int)] = if (end == 0) None else next_chunk(-1)

      def hasNext: Boolean = state.isDefined
      def next(): CharSequence =
        state match {
          case Some((s, i)) => state = next_chunk(i); s
          case None => Iterator.empty.next()
        }
    }

  def space_explode(sep: Char, str: String): List[String] =
    separated_chunks(_ == sep, str).map(_.toString).toList


  /* lines */

  def terminate_lines(lines: TraversableOnce[String]): String = lines.mkString("", "\n", "\n")

  def cat_lines(lines: TraversableOnce[String]): String = lines.mkString("\n")

  def split_lines(str: String): List[String] = space_explode('\n', str)

  def prefix_lines(prfx: String, str: String): String =
    if (str == "") str else cat_lines(split_lines(str).map(prfx + _))

  def first_line(source: CharSequence): String =
  {
    val lines = separated_chunks(_ == '\n', source)
    if (lines.hasNext) lines.next.toString
    else ""
  }

  def trim_line(s: String): String =
    if (s.endsWith("\r\n")) s.substring(0, s.length - 2)
    else if (s.endsWith("\r") || s.endsWith("\n")) s.substring(0, s.length - 1)
    else s

  def trim_split_lines(s: String): List[String] =
    split_lines(trim_line(s)).map(trim_line)

  def encode_lines(s: String): String = s.replace('\n', '\u000b')
  def decode_lines(s: String): String = s.replace('\u000b', '\n')


  /* strings */

  def cat_strings0(strs: TraversableOnce[String]): String = strs.mkString("\u0000")
  def split_strings0(str: String): List[String] = space_explode('\u0000', str)

  def make_string(f: StringBuilder => Unit): String =
  {
    val s = new StringBuilder
    f(s)
    s.toString
  }

  def try_unprefix(prfx: String, s: String): Option[String] =
    if (s.startsWith(prfx)) Some(s.substring(prfx.length)) else None

  def try_unsuffix(sffx: String, s: String): Option[String] =
    if (s.endsWith(sffx)) Some(s.substring(0, s.length - sffx.length)) else None

  def perhaps_unprefix(prfx: String, s: String): String = try_unprefix(prfx, s) getOrElse s
  def perhaps_unsuffix(sffx: String, s: String): String = try_unsuffix(sffx, s) getOrElse s

  def isolate_substring(s: String): String = new String(s.toCharArray)

  def strip_ansi_color(s: String): String =
    s.replaceAll("""\u001b\[\d+m""", "")


  /* quote */

  def single_quote(s: String): String = "'" + s + "'"

  def quote(s: String): String = "\"" + s + "\""

  def try_unquote(s: String): Option[String] =
    if (s.startsWith("\"") && s.endsWith("\"")) Some(s.substring(1, s.length - 1))
    else None

  def perhaps_unquote(s: String): String = try_unquote(s) getOrElse s

  def commas(ss: Iterable[String]): String = ss.iterator.mkString(", ")
  def commas_quote(ss: Iterable[String]): String = ss.iterator.map(quote).mkString(", ")


  /* CharSequence */

  class Reverse(text: CharSequence, start: Int, end: Int) extends CharSequence
  {
    require(0 <= start && start <= end && end <= text.length, "bad reverse range")

    def this(text: CharSequence) = this(text, 0, text.length)

    def length: Int = end - start
    def charAt(i: Int): Char = text.charAt(end - i - 1)

    def subSequence(i: Int, j: Int): CharSequence =
      if (0 <= i && i <= j && j <= length) new Reverse(text, end - j, end - i)
      else throw new IndexOutOfBoundsException

    override def toString: String =
    {
      val buf = new StringBuilder(length)
      for (i <- 0 until length)
        buf.append(charAt(i))
      buf.toString
    }
  }

  class Line_Termination(text: CharSequence) extends CharSequence
  {
    def length: Int = text.length + 1
    def charAt(i: Int): Char = if (i == text.length) '\n' else text.charAt(i)
    def subSequence(i: Int, j: Int): CharSequence =
      if (j == text.length + 1) new Line_Termination(text.subSequence(i, j - 1))
      else text.subSequence(i, j)
    override def toString: String = text.toString + "\n"
  }


  /* regular expressions */

  def make_regex(s: String): Option[Regex] =
    try { Some(new Regex(s)) } catch { case ERROR(_) => None }

  def is_regex_meta(c: Char): Boolean = """()[]{}\^$|?*+.<>-=!""".contains(c)

  def escape_regex(s: String): String =
    if (s.exists(is_regex_meta)) {
      (for (c <- s.iterator)
       yield { if (is_regex_meta(c)) "\\" + c.toString else c.toString }).mkString
    }
    else s


  /* lists */

  def take_prefix[A](pred: A => Boolean, xs: List[A]): (List[A], List[A]) =
    (xs.takeWhile(pred), xs.dropWhile(pred))

  def take_suffix[A](pred: A => Boolean, xs: List[A]): (List[A], List[A]) =
  {
    val rev_xs = xs.reverse
    (rev_xs.dropWhile(pred).reverse, rev_xs.takeWhile(pred).reverse)
  }

  def trim[A](pred: A => Boolean, xs: List[A]): List[A] =
    take_suffix(pred, take_prefix(pred, xs)._2)._1

  def member[A, B](xs: List[A])(x: B): Boolean = xs.contains(x)
  def insert[A](x: A)(xs: List[A]): List[A] = if (xs.contains(x)) xs else x :: xs
  def remove[A, B](x: B)(xs: List[A]): List[A] = if (member(xs)(x)) xs.filterNot(_ == x) else xs
  def update[A](x: A)(xs: List[A]): List[A] = x :: remove(x)(xs)

  def merge[A](xs: List[A], ys: List[A]): List[A] =
    if (xs.eq(ys)) xs
    else if (xs.isEmpty) ys
    else ys.foldRight(xs)(Library.insert(_)(_))

  def distinct[A](xs: List[A], eq: (A, A) => Boolean = (x: A, y: A) => x == y): List[A] =
  {
    val result = new mutable.ListBuffer[A]
    xs.foreach(x => if (!result.exists(y => eq(x, y))) result += x)
    result.toList
  }

  def duplicates[A](lst: List[A], eq: (A, A) => Boolean = (x: A, y: A) => x == y): List[A] =
  {
    val result = new mutable.ListBuffer[A]
    @tailrec def dups(rest: List[A]): Unit =
      rest match {
        case Nil =>
        case x :: xs =>
          if (!result.exists(y => eq(x, y)) && xs.exists(y => eq(x, y))) result += x
          dups(xs)
      }
    dups(lst)
    result.toList
  }

  def replicate[A](n: Int, a: A): List[A] =
    if (n < 0) throw new IllegalArgumentException
    else if (n == 0) Nil
    else {
      val res = new mutable.ListBuffer[A]
      (1 to n).foreach(_ => res += a)
      res.toList
    }


  /* proper values */

  def proper_string(s: String): Option[String] =
    if (s == null || s == "") None else Some(s)

  def proper_list[A](list: List[A]): Option[List[A]] =
    if (list == null || list.isEmpty) None else Some(list)


  /* reflection */

  def is_subclass[A, B](a: Class[A], b: Class[B]): Boolean =
  {
    @tailrec def subclass(c: Class[_]): Boolean =
    {
      c == b ||
        {
          val d = c.getSuperclass
          d != null && subclass(d)
        }
    }
    subclass(a)
  }
}
