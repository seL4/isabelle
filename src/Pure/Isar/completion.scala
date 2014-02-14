/*  Title:      Pure/Isar/completion.scala
    Author:     Makarius

Completion of symbols and keywords.
*/

package isabelle

import scala.collection.immutable.SortedMap
import scala.util.parsing.combinator.RegexParsers
import scala.math.Ordering


object Completion
{
  /* result */

  sealed case class Item(
    original: String,
    replacement: String,
    description: String,
    immediate: Boolean)
  { override def toString: String = description }

  sealed case class Result(original: String, unique: Boolean, items: List[Item])


  /* init */

  val empty: Completion = new Completion()
  def init(): Completion = empty.add_symbols()


  /** persistent history **/

  private val COMPLETION_HISTORY = Path.explode("$ISABELLE_HOME_USER/etc/completion_history")

  object History
  {
    val empty: History = new History()

    def load(): History =
    {
      def ignore_error(msg: String): Unit =
        java.lang.System.err.println("### Ignoring bad content of file " + COMPLETION_HISTORY +
          (if (msg == "") "" else "\n" + msg))

      val content =
        if (COMPLETION_HISTORY.is_file) {
          try {
            import XML.Decode._
            list(pair(Symbol.decode_string, int))(
              YXML.parse_body(File.read(COMPLETION_HISTORY)))
          }
          catch {
            case ERROR(msg) => ignore_error(msg); Nil
            case _: XML.Error => ignore_error(""); Nil
          }
        }
        else Nil
      (empty /: content)(_ + _)
    }
  }

  final class History private(rep: SortedMap[String, Int] = SortedMap.empty)
  {
    override def toString: String = rep.mkString("Completion.History(", ",", ")")

    def frequency(name: String): Int = rep.getOrElse(name, 0)

    def + (entry: (String, Int)): History =
    {
      val (name, freq) = entry
      new History(rep + (name -> (frequency(name) + freq)))
    }

    def ordering: Ordering[Item] =
      new Ordering[Item] {
        def compare(item1: Item, item2: Item): Int =
        {
          frequency(item1.replacement) compare frequency(item2.replacement) match {
            case 0 => item1.replacement compare item2.replacement
            case ord => - ord
          }
        }
      }

    def save()
    {
      Isabelle_System.mkdirs(COMPLETION_HISTORY.dir)
      File.write_backup(COMPLETION_HISTORY,
        {
          import XML.Encode._
          YXML.string_of_body(list(pair(Symbol.encode_string, int))(rep.toList))
        })
    }
  }

  class History_Variable
  {
    private var history = History.empty
    def value: History = synchronized { history }

    def load()
    {
      val h = History.load()
      synchronized { history = h }
    }

    def update(item: Item, freq: Int = 1): Unit = synchronized {
      history = history + (item.replacement -> freq)
    }
  }


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

  def complete(
    history: Completion.History,
    decode: Boolean,
    explicit: Boolean,
    line: CharSequence): Option[Completion.Result] =
  {
    val raw_result =
      Scan.Parsers.parse(Scan.Parsers.literal(abbrevs_lex), new Library.Reverse(line)) match {
        case Scan.Parsers.Success(reverse_a, _) =>
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
                case cs => Some(word, cs)
              }
            case None => None
          }
      }
    raw_result match {
      case Some((word, cs)) =>
        val ds =
          (if (decode) cs.map(Symbol.decode(_)) else cs).filter(_ != word)
        if (ds.isEmpty) None
        else {
          val immediate =
            !Completion.is_word(word) &&
            Character.codePointCount(word, 0, word.length) > 1
          val items = ds.map(s => Completion.Item(word, s, s, explicit || immediate))
          Some(Completion.Result(word, cs.length == 1, items.sorted(history.ordering)))
        }
      case None => None
    }
  }
}
