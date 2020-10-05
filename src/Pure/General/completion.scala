/*  Title:      Pure/General/completion.scala
    Author:     Makarius

Semantic completion within the formal context (reported names).
Syntactic completion of keywords and symbols, with abbreviations
(based on language context).
*/

package isabelle


import scala.collection.immutable.SortedMap
import scala.util.parsing.combinator.RegexParsers
import scala.util.matching.Regex
import scala.math.Ordering


object Completion
{
  /** completion result **/

  sealed case class Item(
    range: Text.Range,
    original: String,
    name: String,
    description: List[String],
    replacement: String,
    move: Int,
    immediate: Boolean)

  object Result
  {
    def empty(range: Text.Range): Result = Result(range, "", false, Nil)
    def merge(history: History, results: Option[Result]*): Option[Result] =
      ((None: Option[Result]) /: results)({
        case (result1, None) => result1
        case (None, result2) => result2
        case (result1 @ Some(res1), Some(res2)) =>
          if (res1.range != res2.range || res1.original != res2.original) result1
          else {
            val items = (res1.items ::: res2.items).sorted(history.ordering)
            Some(Result(res1.range, res1.original, false, items))
          }
      })
  }

  sealed case class Result(
    range: Text.Range,
    original: String,
    unique: Boolean,
    items: List[Item])



  /** persistent history **/

  private val COMPLETION_HISTORY = Path.explode("$ISABELLE_HOME_USER/etc/completion_history")

  object History
  {
    val empty: History = new History()

    def load(): History =
    {
      def ignore_error(msg: String): Unit =
        Output.warning("Ignoring bad content of file " + COMPLETION_HISTORY +
          (if (msg == "") "" else "\n" + msg))

      val content =
        if (COMPLETION_HISTORY.is_file) {
          try {
            import XML.Decode._
            list(pair(string, int))(Symbol.decode_yxml(File.read(COMPLETION_HISTORY)))
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

    def frequency(name: String): Int =
      default_frequency(Symbol.encode(name)) getOrElse
      rep.getOrElse(name, 0)

    def + (entry: (String, Int)): History =
    {
      val (name, freq) = entry
      if (name == "") this
      else new History(rep + (name -> (frequency(name) + freq)))
    }

    def ordering: Ordering[Item] =
      new Ordering[Item] {
        def compare(item1: Item, item2: Item): Int =
          frequency(item2.name) compare frequency(item1.name)
      }

    def save()
    {
      Isabelle_System.make_directory(COMPLETION_HISTORY.dir)
      File.write_backup(COMPLETION_HISTORY,
        {
          import XML.Encode._
          Symbol.encode_yxml(list(pair(string, int))(rep.toList))
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
      history = history + (item.name -> freq)
    }
  }



  /** semantic completion **/

  def clean_name(s: String): Option[String] =
    if (s == "" || s == "_") None
    else Some(s.reverseIterator.dropWhile(_ == '_').toList.reverse.mkString)

  def completed(input: String): String => Boolean =
    clean_name(input) match {
      case None => (name: String) => false
      case Some(prefix) => (name: String) => name.startsWith(prefix)
    }

  def report_no_completion(pos: Position.T): String =
    YXML.string_of_tree(Semantic.Info(pos, No_Completion))

  def report_names(pos: Position.T, names: List[(String, (String, String))], total: Int = 0): String =
    if (names.isEmpty) ""
    else
      YXML.string_of_tree(Semantic.Info(pos, Names(if (total > 0) total else names.length, names)))

  def report_theories(pos: Position.T, thys: List[String], total: Int = 0): String =
    report_names(pos, thys.map(name => (name, ("theory", name))), total)

  object Semantic
  {
    object Info
    {
      def apply(pos: Position.T, semantic: Semantic): XML.Elem =
      {
        val elem =
          semantic match {
            case No_Completion => XML.Elem(Markup(Markup.NO_COMPLETION, pos), Nil)
            case Names(total, names) =>
              XML.Elem(Markup(Markup.COMPLETION, pos),
                {
                  import XML.Encode._
                  pair(int, list(pair(string, pair(string, string))))(total, names)
                })
          }
        XML.Elem(Markup(Markup.REPORT, pos), List(elem))
      }

      def unapply(info: Text.Markup): Option[Text.Info[Semantic]] =
        info.info match {
          case XML.Elem(Markup(Markup.COMPLETION, _), body) =>
            try {
              val (total, names) =
              {
                import XML.Decode._
                pair(int, list(pair(string, pair(string, string))))(body)
              }
              Some(Text.Info(info.range, Names(total, names)))
            }
            catch { case _: XML.Error => None }
          case XML.Elem(Markup(Markup.NO_COMPLETION, _), _) =>
            Some(Text.Info(info.range, No_Completion))
          case _ => None
        }
    }
  }

  sealed abstract class Semantic
  case object No_Completion extends Semantic
  case class Names(total: Int, names: List[(String, (String, String))]) extends Semantic
  {
    def complete(
      range: Text.Range,
      history: Completion.History,
      unicode: Boolean,
      original: String): Option[Completion.Result] =
    {
      def decode(s: String): String = if (unicode) Symbol.decode(s) else s
      val items =
        for {
          (xname, (kind, name)) <- names
          xname1 = decode(xname)
          if xname1 != original
          (full_name, descr_name) =
            if (kind == "") (name, quote(decode(name)))
            else
             (Long_Name.qualify(kind, name),
              Word.implode(Word.explode('_', kind)) +
              (if (xname == name) "" else " " + quote(decode(name))))
        } yield {
          val description = List(xname1, "(" + descr_name + ")")
          val replacement =
            List(original, xname1).map(Token.explode(Keyword.Keywords.empty, _)) match {
              case List(List(tok), _) if tok.kind == Token.Kind.CARTOUCHE =>
                Symbol.cartouche_decoded(xname1)
              case List(_, List(tok)) if tok.is_name => xname1
              case _ => quote(xname1)
            }
          Item(range, original, full_name, description, replacement, 0, true)
        }

      if (items.isEmpty) None
      else Some(Result(range, original, names.length == 1, items.sorted(history.ordering)))
    }
  }



  /** syntactic completion **/

  /* language context */

  object Language_Context
  {
    val outer = Language_Context("", true, false)
    val inner = Language_Context(Markup.Language.UNKNOWN, true, false)
    val ML_outer = Language_Context(Markup.Language.ML, false, true)
    val ML_inner = Language_Context(Markup.Language.ML, true, false)
    val SML_outer = Language_Context(Markup.Language.SML, false, false)
  }

  sealed case class Language_Context(language: String, symbols: Boolean, antiquotes: Boolean)
  {
    def is_outer: Boolean = language == ""
  }


  /* make */

  val empty: Completion = new Completion()

  def make(keywords: List[String], abbrevs: List[(String, String)]): Completion =
    empty.add_symbols.add_keywords(keywords).add_abbrevs(
      Completion.symbol_abbrevs ::: Completion.default_abbrevs ::: abbrevs)


  /* word parsers */

  object Word_Parsers extends RegexParsers
  {
    override val whiteSpace = "".r

    private val symboloid_regex: Regex = """\\([A-Za-z0-9_']+|<\^?[A-Za-z0-9_']+>?)""".r
    def is_symboloid(s: CharSequence): Boolean = symboloid_regex.pattern.matcher(s).matches

    private def reverse_symbol: Parser[String] = """>[A-Za-z0-9_']+\^?<\\""".r
    private def reverse_symb: Parser[String] = """[A-Za-z0-9_']{2,}\^?<\\""".r
    private def reverse_escape: Parser[String] = """[a-zA-Z0-9_']+\\""".r

    private val word_regex = "[a-zA-Z0-9_'.]+".r
    private def word2: Parser[String] = "[a-zA-Z0-9_'.]{2,}".r
    private def underscores: Parser[String] = "_*".r

    def is_word(s: CharSequence): Boolean = word_regex.pattern.matcher(s).matches
    def is_word_char(c: Char): Boolean = Symbol.is_ascii_letdig(c) || c == '.'

    def read_symbol(in: CharSequence): Option[String] =
    {
      val reverse_in = new Library.Reverse(in)
      parse(reverse_symbol ^^ (_.reverse), reverse_in) match {
        case Success(result, _) => Some(result)
        case _ => None
      }
    }

    def read_word(in: CharSequence): Option[(String, String)] =
    {
      val reverse_in = new Library.Reverse(in)
      val parser =
        (reverse_symbol | reverse_symb | reverse_escape) ^^ (x => (x.reverse, "")) |
        underscores ~ word2 ~ opt("?") ^^
        { case x ~ y ~ z => (z.getOrElse("") + y.reverse, x) }
      parse(parser, reverse_in) match {
        case Success(result, _) => Some(result)
        case _ => None
      }
    }
  }


  /* templates */

  val caret_indicator = '\u0007'

  def split_template(s: String): (String, String) =
    space_explode(caret_indicator, s) match {
      case List(s1, s2) => (s1, s2)
      case _ => (s, "")
    }


  /* abbreviations */

  private def symbol_abbrevs: Thy_Header.Abbrevs =
    for ((sym, abbr) <- Symbol.abbrevs.toList) yield (abbr, sym)

  private val antiquote = "@{"

  private val default_abbrevs =
    List("@{" -> "@{\u0007}",
      "`" -> "\\<close>",
      "`" -> "\\<open>",
      "`" -> "\\<open>\u0007\\<close>",
      "\"" -> "\\<close>",
      "\"" -> "\\<open>",
      "\"" -> "\\<open>\u0007\\<close>")

  private def default_frequency(name: String): Option[Int] =
    default_abbrevs.iterator.map(_._2).zipWithIndex.find(_._1 == name).map(_._2)
}

final class Completion private(
  keywords: Set[String] = Set.empty,
  words_lex: Scan.Lexicon = Scan.Lexicon.empty,
  words_map: Multi_Map[String, String] = Multi_Map.empty,
  abbrevs_lex: Scan.Lexicon = Scan.Lexicon.empty,
  abbrevs_map: Multi_Map[String, (String, String)] = Multi_Map.empty)
{
  /* keywords */

  private def is_symbol(name: String): Boolean = Symbol.names.isDefinedAt(name)
  private def is_keyword(name: String): Boolean = !is_symbol(name) && keywords(name)
  private def is_keyword_template(name: String, template: Boolean): Boolean =
    is_keyword(name) && (words_map.getOrElse(name, name) != name) == template

  def add_keyword(keyword: String): Completion =
    new Completion(keywords + keyword, words_lex, words_map, abbrevs_lex, abbrevs_map)

  def add_keywords(names: List[String]): Completion =
  {
    val keywords1 = (keywords /: names) { case (ks, k) => if (ks(k)) ks else ks + k }
    if (keywords eq keywords1) this
    else new Completion(keywords1, words_lex, words_map, abbrevs_lex, abbrevs_map)
  }


  /* symbols and abbrevs */

  def add_symbols: Completion =
  {
    val words =
      Symbol.names.toList.flatMap({ case (sym, (name, argument)) =>
        val word = "\\" + name
        val seps =
          if (argument == Symbol.ARGUMENT_CARTOUCHE) List("")
          else if (argument == Symbol.ARGUMENT_SPACE_CARTOUCHE) List(" ")
          else Nil
        List(sym -> sym, word -> sym) :::
          seps.map(sep => word -> (sym + sep + "\\<open>\u0007\\<close>"))
      })

    new Completion(
      keywords,
      words_lex ++ words.map(_._1),
      words_map ++ words,
      abbrevs_lex,
      abbrevs_map)
  }

  def add_abbrevs(abbrevs: List[(String, String)]): Completion =
    (this /: abbrevs)(_.add_abbrev(_))

  private def add_abbrev(abbrev: (String, String)): Completion =
    abbrev match {
      case ("", _) => this
      case (abbr, text) =>
        val rev_abbr = abbr.reverse
        val is_word = Completion.Word_Parsers.is_word(abbr)

        val (words_lex1, words_map1) =
          if (!is_word) (words_lex, words_map)
          else if (text != "") (words_lex + abbr, words_map + abbrev)
          else (words_lex -- List(abbr), words_map - abbr)

        val (abbrevs_lex1, abbrevs_map1) =
          if (is_word) (abbrevs_lex, abbrevs_map)
          else if (text != "") (abbrevs_lex + rev_abbr, abbrevs_map + (rev_abbr -> abbrev))
          else (abbrevs_lex -- List(rev_abbr), abbrevs_map - rev_abbr)

        new Completion(keywords, words_lex1, words_map1, abbrevs_lex1, abbrevs_map1)
    }


  /* complete */

  def complete(
    history: Completion.History,
    unicode: Boolean,
    explicit: Boolean,
    start: Text.Offset,
    text: CharSequence,
    caret: Int,
    language_context: Completion.Language_Context): Option[Completion.Result] =
  {
    val length = text.length

    val abbrevs_result =
    {
      val reverse_in = new Library.Reverse(text.subSequence(0, caret))
      Scan.Parsers.parse(Scan.Parsers.literal(abbrevs_lex), reverse_in) match {
        case Scan.Parsers.Success(reverse_abbr, _) =>
          val abbrevs = abbrevs_map.get_list(reverse_abbr)
          abbrevs match {
            case Nil => None
            case (abbr, _) :: _ =>
              val ok =
                if (abbr == Completion.antiquote) language_context.antiquotes
                else language_context.symbols || Completion.default_abbrevs.exists(_._1 == abbr)
              if (ok) Some((abbr, abbrevs))
              else None
          }
        case _ => None
      }
    }

    val words_result =
      if (abbrevs_result.isDefined) None
      else {
        val word_context =
          caret < length && Completion.Word_Parsers.is_word_char(text.charAt(caret))
        val result =
          Completion.Word_Parsers.read_symbol(text.subSequence(0, caret)) match {
            case Some(symbol) => Some((symbol, ""))
            case None => Completion.Word_Parsers.read_word(text.subSequence(0, caret))
          }
        result.map(
          {
            case (word, underscores) =>
              val complete_words = words_lex.completions(word)
              val full_word = word + underscores
              val completions =
                if (complete_words.contains(full_word) && is_keyword_template(full_word, false)) Nil
                else
                  for {
                    complete_word <- complete_words
                    ok =
                      if (is_keyword(complete_word)) !word_context && language_context.is_outer
                      else language_context.symbols || Completion.Word_Parsers.is_symboloid(word)
                    if ok
                    completion <- words_map.get_list(complete_word)
                  } yield (complete_word, completion)
              (full_word, completions)
          })
      }

    (abbrevs_result orElse words_result) match {
      case Some((original, completions)) if completions.nonEmpty =>
        val range = Text.Range(- original.length, 0) + caret + start
        val immediate =
          explicit ||
            (!Completion.Word_Parsers.is_word(original) &&
             !Completion.Word_Parsers.is_symboloid(original) &&
              Character.codePointCount(original, 0, original.length) > 1)
        val unique = completions.length == 1

        def decode1(s: String): String = if (unicode) Symbol.decode(s) else s
        def decode2(s: String): String = if (unicode) s else Symbol.decode(s)

        val items =
          for {
            (complete_word, name0) <- completions
            name1 = decode1(name0)
            name2 = decode2(name0)
            if name1 != original
            (s1, s2) = Completion.split_template(name1)
            move = - s2.length
            description =
              if (is_symbol(name0)) {
                if (name1 == name2) List(name1)
                else List(name1, "(symbol " + quote(name2) + ")")
              }
              else if (is_keyword_template(complete_word, true))
                List(name1, "(template " + quote(complete_word) + ")")
              else if (move != 0) List(name1, "(template)")
              else if (is_keyword(complete_word)) List(name1, "(keyword)")
              else List(name1)
          }
          yield Completion.Item(range, original, name1, description, s1 + s2, move, immediate)

        if (items.isEmpty) None
        else
          Some(Completion.Result(range, original, unique,
            items.sortBy(_.name).sorted(history.ordering)))

      case _ => None
    }
  }
}
