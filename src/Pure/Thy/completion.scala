/*  Title:      Pure/Thy/completion.scala
    Author:     Makarius

Completion of symbols and keywords.
*/

package isabelle

import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers


private object Completion
{
  /** word completion **/

  val word_regex = "[a-zA-Z0-9_']+".r
  def is_word(s: CharSequence): Boolean = word_regex.pattern.matcher(s).matches

  object Parse extends RegexParsers
  {
    override val whiteSpace = "".r

    def reverse_symbol: Parser[String] = """>[A-Za-z0-9_']+\^?<\\""".r
    def reverse_symb: Parser[String] = """[A-Za-z0-9_']{2,}\^?<\\""".r
    def word: Parser[String] = "[a-zA-Z0-9_']{2,}".r

    def read(in: CharSequence): Option[String] =
    {
      val reverse_in = new Library.Reverse(in)
      parse((reverse_symbol | reverse_symb | word) ^^ (_.reverse), reverse_in) match {
        case Success(result, _) => Some(result)
        case _ => None
      }
    }
  }
}

class Completion
{
  /* representation */

  protected val words_lex = Scan.Lexicon()
  protected val words_map = Map[String, String]()

  protected val abbrevs_lex = Scan.Lexicon()
  protected val abbrevs_map = Map[String, (String, String)]()


  /* adding stuff */

  def + (keyword: String, replace: String): Completion =
  {
    val old = this
    new Completion {
      override val words_lex = old.words_lex + keyword
      override val words_map = old.words_map + (keyword -> replace)
      override val abbrevs_lex = old.abbrevs_lex
      override val abbrevs_map = old.abbrevs_map
    }
  }

  def + (keyword: String): Completion = this + (keyword, keyword)

  def add_symbols: Completion =
  {
    val words =
      (for ((x, _) <- Symbol.names) yield (x, x)).toList :::
      (for ((x, y) <- Symbol.names) yield (y, x)).toList :::
      (for ((x, y) <- Symbol.abbrevs if Completion.is_word(y)) yield (y, x)).toList

    val abbrs =
      (for ((x, y) <- Symbol.abbrevs if !Completion.is_word(y))
        yield (y.reverse.toString, (y, x))).toList

    val old = this
    new Completion {
      override val words_lex = old.words_lex ++ words.map(_._1)
      override val words_map = old.words_map ++ words
      override val abbrevs_lex = old.abbrevs_lex ++ abbrs.map(_._1)
      override val abbrevs_map = old.abbrevs_map ++ abbrs
    }
  }


  /* complete */

  def complete(line: CharSequence): Option[(String, List[String])] =
  {
    abbrevs_lex.parse(abbrevs_lex.keyword, new Library.Reverse(line)) match {
      case abbrevs_lex.Success(reverse_a, _) =>
        val (word, c) = abbrevs_map(reverse_a)
        Some(word, List(c))
      case _ =>
        Completion.Parse.read(line) match {
          case Some(word) =>
            words_lex.completions(word).map(words_map(_)) match {
              case Nil => None
              case cs => Some(word, cs.sorted)
            }
          case None => None
        }
    }
  }
}
