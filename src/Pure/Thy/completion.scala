/*  Title:      Pure/Thy/completion.scala
    Author:     Makarius

Completion of symbols and keywords.
*/

package isabelle

import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers


object Completion
{
  val empty: Completion =
    new Completion(Scan.Lexicon(), Map.empty, Scan.Lexicon(), Map.empty)

  def init(): Completion = empty.add_symbols()


  /** word completion **/

  private val word_regex = "[a-zA-Z0-9_']+".r
  private def is_word(s: CharSequence): Boolean = word_regex.pattern.matcher(s).matches

  private object Parse extends RegexParsers
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

class Completion private(
  words_lex: Scan.Lexicon,
  words_map: Map[String, String],
  abbrevs_lex: Scan.Lexicon,
  abbrevs_map: Map[String, (String, String)])
{
  /* adding stuff */

  def + (keyword: String, replace: String): Completion =
    new Completion(
      words_lex + keyword,
      words_map + (keyword -> replace),
      abbrevs_lex,
      abbrevs_map)

  def + (keyword: String): Completion = this + (keyword, keyword)

  private def add_symbols(): Completion =
  {
    val words =
      (for ((x, _) <- Symbol.names) yield (x, x)).toList :::
      (for ((x, y) <- Symbol.names) yield (y, x)).toList :::
      (for ((x, y) <- Symbol.abbrevs if Completion.is_word(y)) yield (y, x)).toList

    val abbrs =
      (for ((x, y) <- Symbol.abbrevs if !Completion.is_word(y))
        yield (y.reverse.toString, (y, x))).toList

    new Completion(
      words_lex ++ words.map(_._1),
      words_map ++ words,
      abbrevs_lex ++ abbrs.map(_._1),
      abbrevs_map ++ abbrs)
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
