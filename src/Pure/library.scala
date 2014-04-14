/*  Title:      Pure/library.scala
    Module:     PIDE
    Author:     Makarius

Basic library.
*/

package isabelle


import scala.collection.mutable

import java.util.Locale
import java.util.concurrent.{Future => JFuture, TimeUnit}


object Library
{
  /* user errors */

  object ERROR
  {
    def apply(message: String): Throwable = new RuntimeException(message)
    def unapply(exn: Throwable): Option[String] = Exn.user_message(exn)
  }

  def error(message: String): Nothing = throw ERROR(message)

  def cat_message(msg1: String, msg2: String): String =
    if (msg1 == "") msg2
    else msg1 + "\n" + msg2

  def cat_error(msg1: String, msg2: String): Nothing =
    error(cat_message(msg1, msg2))


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

  def separated_chunks(sep: Char, source: CharSequence): Iterator[CharSequence] =
    new Iterator[CharSequence] {
      private val end = source.length
      private def next_chunk(i: Int): Option[(CharSequence, Int)] =
      {
        if (i < end) {
          var j = i; do j += 1 while (j < end && source.charAt(j) != sep)
          Some((source.subSequence(i + 1, j), j))
        }
        else None
      }
      private var state: Option[(CharSequence, Int)] = if (end == 0) None else next_chunk(-1)

      def hasNext(): Boolean = state.isDefined
      def next(): CharSequence =
        state match {
          case Some((s, i)) => { state = next_chunk(i); s }
          case None => Iterator.empty.next()
        }
    }

  def space_explode(sep: Char, str: String): List[String] =
    separated_chunks(sep, str).map(_.toString).toList


  /* lines */

  def terminate_lines(lines: Iterable[CharSequence]): Iterable[CharSequence] =
    new Iterable[CharSequence] {
      def iterator: Iterator[CharSequence] =
        lines.iterator.map(line => new Line_Termination(line))
    }

  def cat_lines(lines: TraversableOnce[String]): String = lines.mkString("\n")

  def split_lines(str: String): List[String] = space_explode('\n', str)

  def first_line(source: CharSequence): String =
  {
    val lines = separated_chunks('\n', source)
    if (lines.hasNext) lines.next.toString
    else ""
  }

  def plain_words(str: String): String =
    space_explode('_', str).mkString(" ")


  /* strings */

  def lowercase(str: String): String = str.toLowerCase(Locale.ROOT)
  def uppercase(str: String): String = str.toUpperCase(Locale.ROOT)

  def capitalize(str: String): String =
    if (str.length == 0) str
    else uppercase(str.substring(0, 1)) + str.substring(1)

  def is_capitalized(str: String): Boolean =
    str.length > 0 &&
    Character.isUpperCase(str(0)) && str.substring(1).forall(Character.isLowerCase(_))

  def is_all_caps(str: String): Boolean =
    str.length > 0 && str.forall(Character.isUpperCase(_))

  def try_unprefix(prfx: String, s: String): Option[String] =
    if (s.startsWith(prfx)) Some(s.substring(prfx.length)) else None

  def try_unsuffix(sffx: String, s: String): Option[String] =
    if (s.endsWith(sffx)) Some(s.substring(0, s.length - sffx.length)) else None

  def trim_line(s: String): String =
    if (s.endsWith("\r\n")) s.substring(0, s.length - 2)
    else if (s.endsWith("\r") || s.endsWith("\n")) s.substring(0, s.length - 1)
    else s


  /* quote */

  def quote(s: String): String = "\"" + s + "\""
  def commas(ss: Iterable[String]): String = ss.iterator.mkString(", ")
  def commas_quote(ss: Iterable[String]): String = ss.iterator.map(quote).mkString(", ")


  /* CharSequence */

  class Reverse(text: CharSequence, start: Int, end: Int) extends CharSequence
  {
    require(0 <= start && start <= end && end <= text.length)

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


  /* Java futures */

  def future_value[A](x: A) = new JFuture[A]
  {
    def cancel(may_interrupt: Boolean): Boolean = false
    def isCancelled(): Boolean = false
    def isDone(): Boolean = true
    def get(): A = x
    def get(timeout: Long, time_unit: TimeUnit): A = x
  }
}


class Basic_Library
{
  val ERROR = Library.ERROR
  val error = Library.error _
  val cat_error = Library.cat_error _

  val space_explode = Library.space_explode _
  val split_lines = Library.split_lines _
  val cat_lines = Library.cat_lines _
  val quote = Library.quote _
  val commas = Library.commas _
  val commas_quote = Library.commas_quote _


  /* parallel tasks */

  implicit def function_as_callable[A](f: () => A) =
    new java.util.concurrent.Callable[A] { def call = f() }

  val default_thread_pool =
    scala.collection.parallel.ThreadPoolTasks.defaultThreadPool
}
