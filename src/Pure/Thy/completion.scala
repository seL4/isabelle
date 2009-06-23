/*  Title:      Pure/Thy/completion.scala
    Author:     Makarius

Completion of symbols and keywords.
*/

package isabelle

import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers


private object Completion
{
  /** String/CharSequence utilities */

  def length_ord(s1: String, s2: String): Boolean =
    s1.length < s2.length || s1.length == s2.length && s1 <= s2

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
      val buf = new StringBuffer(length)
      for (i <- 0 until length)
        buf.append(charAt(i))
      buf.toString
    }
  }


  /** word completion **/

  val word_regex = "[a-zA-Z0-9_']+".r
  def is_word(s: CharSequence): Boolean = word_regex.pattern.matcher(s).matches

  object Parse extends RegexParsers
  {
    override val whiteSpace = "".r

    def rev_symb: Parser[String] = """>?[A-Za-z0-9_']+<\\""".r
    def word: Parser[String] = "[a-zA-Z0-9_']{3,}".r

    def read(in: CharSequence): Option[String] =
    {
      parse((rev_symb | word) ^^ (_.reverse), new Reverse(in)) match {
        case Success(result, _) => Some(result)
        case _ => None
      }
    }
  }

}

class Completion
{
  /* representation */

  val words_lex = Scan.Lexicon()
  val words_map = Map[String, String]()

  val abbrevs_lex = Scan.Lexicon()
  val abbrevs_map = Map[String, (String, String)]()


  /* adding stuff */

  def + (keyword: String): Completion =
  {
    val old = this
    new Completion {
      override val words_lex = old.words_lex + keyword
      override val words_map = old.words_map + (keyword -> keyword)
      override val abbrevs_lex = old.abbrevs_lex
      override val abbrevs_map = old.abbrevs_map
    }
  }

  def + (symbols: Symbol.Interpretation): Completion =
  {
    val words =
      (for ((x, _) <- symbols.names) yield (x, x)).toList :::
      (for ((x, y) <- symbols.names) yield (y, x)).toList :::
      (for ((x, y) <- symbols.abbrevs if Completion.is_word(y)) yield (y, x)).toList

    val abbrs =
      (for ((x, y) <- symbols.abbrevs if !Completion.is_word(y))
        yield (y.reverse.toString, (y, symbols.decode(x)))).toList

    val old = this
    new Completion {
      override val words_lex = old.words_lex ++ words.map(_._1)
      override val words_map = old.words_map ++ words.map(p => (p._1, symbols.decode(p._2)))
      override val abbrevs_lex = old.abbrevs_lex ++ abbrs.map(_._1)
      override val abbrevs_map = old.abbrevs_map ++ abbrs
    }
  }


  /* complete */

  def complete(line: CharSequence): List[(String, String)] =
  {
    val abbrs =
      abbrevs_lex.parse(abbrevs_lex.keyword, new Completion.Reverse(line)) match {
        case abbrevs_lex.Success(rev_a, _) => List(abbrevs_map(rev_a))
        case _ => Nil
      }

    val compls =
      Completion.Parse.read(line) match {
        case Some(word) => words_lex.completions(word).map(w => (word, words_map(w)))
        case _ => Nil
      }

    (abbrs ::: compls).sort((p1, p2) => Completion.length_ord(p1._2, p2._2))
  }

}
