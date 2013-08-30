/*  Title:      Pure/Isar/completion.scala
    Author:     Makarius

Completion of symbols and keywords.
*/

package isabelle

import scala.util.parsing.combinator.RegexParsers


object Completion
{
  /* items */

  sealed case class Item(
    original: String,
    replacement: String,
    description: String,
    immediate: Boolean)
  { override def toString: String = description }


  /* init */

  val empty: Completion = new Completion()
  def init(): Completion = empty.add_symbols()


  /** word completion **/

  private val word_regex = "[a-zA-Z0-9_']+".r
  private def is_word(s: CharSequence): Boolean = word_regex.pattern.matcher(s).matches

  private object Parse extends RegexParsers
  {
    override val whiteSpace = "".r

    def reverse_symbol: Parser[String] = """>[A-Za-z0-9_']+\^?<\\""".r
    def reverse_symb: Parser[String] = """[A-Za-z0-9_']{2,}\^?<\\""".r
    def escape: Parser[String] = """[a-zA-Z0-9_']+\\""".r
    def word: Parser[String] = word_regex
    def word3: Parser[String] = """[a-zA-Z0-9_']{3,}""".r

    def read(explicit: Boolean, in: CharSequence): Option[String] =
    {
      val parse_word = if (explicit) word else word3
      val reverse_in = new Library.Reverse(in)
      parse((reverse_symbol | reverse_symb | escape | parse_word) ^^ (_.reverse), reverse_in) match {
        case Success(result, _) => Some(result)
        case _ => None
      }
    }
  }
}

final class Completion private(
  words_lex: Scan.Lexicon = Scan.Lexicon.empty,
  words_map: Multi_Map[String, String] = Multi_Map.empty,
  abbrevs_lex: Scan.Lexicon = Scan.Lexicon.empty,
  abbrevs_map: Multi_Map[String, (String, String)] = Multi_Map.empty)
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
      (for ((x, y) <- Symbol.names) yield ("\\" + y, x)).toList :::
      (for ((x, y) <- Symbol.abbrevs.iterator if Completion.is_word(y)) yield (y, x)).toList

    val abbrs =
      (for ((x, y) <- Symbol.abbrevs.iterator if !Completion.is_word(y))
        yield (y.reverse.toString, (y, x))).toList

    new Completion(
      words_lex ++ words.map(_._1),
      words_map ++ words,
      abbrevs_lex ++ abbrs.map(_._1),
      abbrevs_map ++ abbrs)
  }


  /* complete */

  def complete(decode: Boolean, explicit: Boolean, line: CharSequence)
    : Option[(String, List[Completion.Item])] =
  {
    val raw_result =
      abbrevs_lex.parse(abbrevs_lex.keyword, new Library.Reverse(line)) match {
        case abbrevs_lex.Success(reverse_a, _) =>
          val abbrevs = abbrevs_map.get_list(reverse_a)
          abbrevs match {
            case Nil => None
            case (a, _) :: _ => Some((a, abbrevs.map(_._2)))
          }
        case _ =>
          Completion.Parse.read(explicit, line) match {
            case Some(word) =>
              words_lex.completions(word).map(words_map.get_list(_)).flatten match {
                case Nil => None
                case cs => Some(word, cs.sorted)
              }
            case None => None
          }
      }
    raw_result match {
      case Some((word, cs)) =>
        val ds = (if (decode) cs.map(Symbol.decode(_)).sorted else cs)
        if (ds.isEmpty) None
        else {
          val immediate =
            !Completion.is_word(word) &&
            Character.codePointCount(word, 0, word.length) > 1
          Some((word, ds.map(s => Completion.Item(word, s, s, immediate))))
        }
      case None => None
    }
  }
}
