/*  Title:      Pure/General/symbol.scala
    Author:     Makarius

Isabelle text symbols.
*/

package isabelle


import scala.collection.mutable
import scala.util.matching.Regex
import scala.annotation.tailrec


object Symbol {
  type Symbol = String

  // counting Isabelle symbols, starting from 1
  type Offset = Text.Offset
  type Range = Text.Range


  /* spaces */

  val space_char = ' '
  val space = " "

  private val static_spaces = space * 4000

  def spaces(n: Int): String = {
    require(n >= 0, "negative spaces")
    if (n < static_spaces.length) static_spaces.substring(0, n)
    else space * n
  }


  /* char symbols */

  private val char_symbols: Array[Symbol] =
    (0 until 0x500).iterator.map(i => new String(Array(i.toChar))).toArray

  def char_symbol(c: Char): String =
    if (c < char_symbols.length) char_symbols(c)
    else c.toString


  /* ASCII characters */

  def is_ascii_printable(c: Char): Boolean = space_char <= c && c <= '~'

  def is_ascii_letter(c: Char): Boolean = 'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z'

  def is_ascii_digit(c: Char): Boolean = '0' <= c && c <= '9'

  def is_ascii_hex(c: Char): Boolean =
    '0' <= c && c <= '9' || 'A' <= c && c <= 'F' || 'a' <= c && c <= 'f'

  def is_ascii_quasi(c: Char): Boolean = c == '_' || c == '\''

  def is_ascii_blank(c: Char): Boolean = " \t\n\u000b\f\r".contains(c)

  def is_ascii_line_terminator(c: Char): Boolean = "\r\n".contains(c)

  def is_ascii_letdig(c: Char): Boolean =
    is_ascii_letter(c) || is_ascii_digit(c) || is_ascii_quasi(c)

  def is_ascii_identifier(s: String): Boolean =
    s.nonEmpty && is_ascii_letter(s(0)) && s.forall(is_ascii_letdig)

  def ascii(c: Char): Symbol = {
    if (c > 127) error("Non-ASCII character: " + quote(c.toString))
    else char_symbol(c)
  }

  def is_ascii(s: Symbol): Boolean = s.length == 1 && s(0) < 128


  /* symbol matching */

  def is_malformed(s: Symbol): Boolean =
    s.length match {
      case 1 =>
        val c = s(0)
        Character.isHighSurrogate(c) || Character.isLowSurrogate(c) || c == '\ufffd'
      case 2 =>
        val c1 = s(0)
        val c2 = s(1)
        !(c1 == '\r' && c2 == '\n' || Character.isSurrogatePair(c1, c2))
      case _ => !s.endsWith(">") || s == "\\<>" || s == "\\<^>"
    }

  def is_newline(s: Symbol): Boolean =
    s == "\n" || s == "\r" || s == "\r\n"

  class Matcher(text: CharSequence) {
    private def ok(i: Int): Boolean = 0 <= i && i < text.length
    private def char(i: Int): Char = if (ok(i)) text.charAt(i) else 0
    private def maybe_char(c: Char, i: Int): Int = if (char(i) == c) i + 1 else i

    @tailrec private def many_ascii_letdig(i: Int): Int =
      if (is_ascii_letdig(char(i))) many_ascii_letdig(i + 1) else i
    private def maybe_ascii_id(i: Int): Int =
      if (is_ascii_letter(char(i))) many_ascii_letdig(i + 1) else i

    def match_length(i: Int): Int = {
      val a = char(i)
      val b = char(i + 1)

      if (Character.isHighSurrogate(a) && Character.isLowSurrogate(b) || a == '\r' && b == '\n') 2
      else if (a == '\\' && b == '<') maybe_char('>', maybe_ascii_id(maybe_char('^', i + 2))) - i
      else if (ok(i)) 1
      else 0
    }

    def match_symbol(i: Int): String =
      match_length(i) match {
        case 0 => ""
        case 1 => char_symbol(text.charAt(i))
        case n => text.subSequence(i, i + n).toString
      }
  }


  /* iterator */

  def iterator(text: CharSequence): Iterator[Symbol] =
    new Iterator[Symbol] {
      private val matcher = new Matcher(text)
      private var i = 0
      def hasNext: Boolean = i < text.length
      def next(): Symbol = {
        val s = matcher.match_symbol(i)
        i += s.length
        s
      }
    }

  def explode(text: CharSequence): List[Symbol] = iterator(text).toList

  def length(text: CharSequence): Int = iterator(text).length

  def trim_blanks(text: CharSequence): String =
    Library.trim(is_blank, explode(text)).mkString

  def all_blank(str: String): Boolean =
    iterator(str).forall(is_blank)

  def trim_blank_lines(text: String): String =
    cat_lines(split_lines(text).dropWhile(all_blank).reverse.dropWhile(all_blank).reverse)


  /* decoding offsets */

  object Index {
    private sealed case class Entry(chr: Int, sym: Int)

    val empty: Index = new Index(Nil)

    def apply(text: CharSequence): Index = {
      val matcher = new Matcher(text)
      val buf = new mutable.ListBuffer[Entry]
      var chr = 0
      var sym = 0
      while (chr < text.length) {
        val n = matcher.match_length(chr)
        chr += n
        sym += 1
        if (n > 1) buf += Entry(chr, sym)
      }
      if (buf.isEmpty) empty else new Index(buf.toList)
    }
  }

  final class Index private(entries: List[Index.Entry]) {
    private val hash: Int = entries.hashCode
    private val index: Array[Index.Entry] = entries.toArray

    def decode(symbol_offset: Offset): Text.Offset = {
      val sym = symbol_offset - 1
      val end = index.length
      @tailrec def bisect(a: Int, b: Int): Int = {
        if (a < b) {
          val c = (a + b) / 2
          if (sym < index(c).sym) bisect(a, c)
          else if (c + 1 == end || sym < index(c + 1).sym) c
          else bisect(c + 1, b)
        }
        else -1
      }
      val i = bisect(0, end)
      if (i < 0) sym
      else index(i).chr + sym - index(i).sym
    }
    def decode(symbol_range: Range): Text.Range = symbol_range.map(decode)

    override def hashCode: Int = hash
    override def equals(that: Any): Boolean =
      that match {
        case other: Index => index.sameElements(other.index)
        case _ => false
      }
  }


  /* symbolic text chunks -- without actual text */

  object Text_Chunk {
    sealed abstract class Name
    case object Default extends Name
    case class Id(id: Document_ID.Generic) extends Name
    case class File(name: String) extends Name

    def apply(text: CharSequence): Text_Chunk =
      new Text_Chunk(Text.Range.length(text), Index(text))
  }

  final class Text_Chunk private(val range: Text.Range, private val index: Index) {
    override def hashCode: Int = (range, index).hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Text_Chunk =>
          range == other.range &&
          index == other.index
        case _ => false
      }

    override def toString: String = "Text_Chunk" + range.toString

    def decode(symbol_offset: Offset): Text.Offset = index.decode(symbol_offset)
    def decode(symbol_range: Range): Text.Range = index.decode(symbol_range)
    def incorporate(symbol_range: Range): Option[Text.Range] = {
      def in(r: Range): Option[Text.Range] = {
        range.try_restrict(decode(r)) match {
          case Some(r1) if !r1.is_singularity => Some(r1)
          case _ => None
        }
      }
      in(symbol_range) orElse in(symbol_range - 1)
    }
  }


  /* recoding text */

  private class Recoder(list: List[(String, String)]) {
    private val (min, max) = {
      var min = '\uffff'
      var max = '\u0000'
      for ((x, _) <- list) {
        val c = x(0)
        if (c < min) min = c
        if (c > max) max = c
      }
      (min, max)
    }
    private val table = {
      var tab = Map[String, String]()
      for ((x, y) <- list) {
        tab.get(x) match {
          case None => tab += (x -> y)
          case Some(z) =>
            error("Duplicate symbol mapping of " + quote(x) + " to " + quote(y) + " vs. " + quote(z))
        }
      }
      tab
    }
    def recode(text: String): String = {
      val n = text.length
      val relevant = {
        var i = 0
        var found = false
        while (i < n && !found) {
          val c = text(i)
          if (min <= c && c <= max) { found = true }
          i += 1
        }
        found
      }
      if (relevant) {
        val matcher = new Symbol.Matcher(text)
        Library.string_builder(hint = n) { result =>
          var i = 0
          while (i < n) {
            val c = text(i)
            if (min <= c && c <= max) {
              val s = matcher.match_symbol(i)
              result.append(table.getOrElse(s, s))
              i += s.length
            }
            else { result.append(c); i += 1 }
          }
        }
      }
      else text
    }
  }



  /** defined symbols **/

  object Argument {
    def unapply(s: String): Option[Argument] =
      try { Some(valueOf(s)) }
      catch { case _: IllegalArgumentException => None}
  }

  enum Argument { case none, cartouche, space_cartouche }

  object Entry {
    private val Name = new Regex("""\\<\^?([A-Za-z][A-Za-z0-9_']*)>""")
    private val Argument = new Properties.String("argument")
    private val Abbrev = new Properties.String("abbrev")
    private val Code = new Properties.String("code")
    private val Font = new Properties.String("font")
    private val Group = new Properties.String("group")

    def apply(symbol: Symbol, props: Properties.T): Entry = {
      def err(msg: String): Nothing = error(msg + " for symbol " + quote(symbol))

      val name =
        symbol match { case Name(a) => a case _ => err("Cannot determine name") }

      val argument =
        props match {
          case Argument(arg) =>
            Symbol.Argument.unapply(arg) getOrElse
              error("Bad argument: " + quote(arg) + " for symbol " + quote(symbol))
          case _ => Symbol.Argument.none
        }

      val code =
        props match {
          case Code(s) =>
            try {
              val code = Integer.decode(s).intValue
              if (code >= 128) Some(code) else err("Illegal ASCII code")
            }
            catch { case _: NumberFormatException => err("Bad code") }
          case _ => None
        }

      val groups =
        proper_list(for (case (Group.name, a) <- props) yield a).getOrElse(List("unsorted"))

      val abbrevs = for (case (Abbrev.name, a) <- props) yield a

      new Entry(symbol, name, argument, code, Font.unapply(props), groups, abbrevs)
    }
  }

  class Entry private(
    val symbol: Symbol,
    val name: String,
    val argument: Symbol.Argument,
    val code: Option[Int],
    val font: Option[String],
    val groups: List[String],
    val abbrevs: List[String]
  ) {
    override def toString: String = symbol

    val decode: Option[String] =
      code.map(c => new String(Character.toChars(c)))
  }

  lazy val symbols: Symbols =
    Symbols.make(cat_lines(Symbols.files().map(File.read)))

  object Symbols {
    def files(): List[Path] =
      Path.split_permissive_files(Isabelle_System.getenv("ISABELLE_SYMBOLS"))

    def make(symbols_spec: String): Symbols = {
      val No_Decl = new Regex("""(?xs) ^\s* (?: \#.* )? $ """)
      val Key = new Regex("""(?xs) (.+): """)

      def read_decl(decl: String): (Symbol, Properties.T) = {
        def err() = error("Bad symbol declaration: " + decl)

        def read_props(props: List[String]): Properties.T = {
          props match {
            case Nil => Nil
            case _ :: Nil => err()
            case Key(x) :: y :: rest => (x -> y.replace('\u2423', ' ')) :: read_props(rest)
            case _ => err()
          }
        }
        decl.split("\\s+").toList match {
          case sym :: props if sym.length > 1 && !is_malformed(sym) =>
            (sym, read_props(props))
          case _ => err()
        }
      }

      new Symbols(
        split_lines(symbols_spec).reverse.
          foldLeft((List.empty[Entry], Set.empty[Symbol])) {
            case (res, No_Decl()) => res
            case ((list, known), decl) =>
              val (sym, props) = read_decl(decl)
              if (known(sym)) (list, known)
              else (Entry(sym, props) :: list, known + sym)
          }._1)
    }
  }

  class Symbols(val entries: List[Entry]) {
    override def toString: String = entries.mkString("Symbols(", ", ", ")")


    /* basic properties */

    private val entries_map: Map[Symbol, Entry] =
      (for (entry <- entries.iterator) yield entry.symbol -> entry).toMap

    def get(sym: Symbol): Option[Entry] = entries_map.get(sym)
    def defined(sym: Symbol): Boolean = entries_map.isDefinedAt(sym)

    def defined_code(sym: Symbol): Boolean =
      get(sym) match { case Some(entry) => entry.code.isDefined case _ => false }

    val code_defined: Int => Boolean =
      (for (entry <- entries.iterator; code <- entry.code) yield code).toSet

    val groups_code: List[(String, List[Symbol])] =
      (for {
        entry <- entries.iterator if entry.code.isDefined
        group <- entry.groups.iterator
      } yield entry.symbol -> group)
        .toList.groupBy(_._2).toList.map({ case (g, list) => (g, list.map(_._1)) }).sortBy(_._1)

    def get_abbrevs(sym: Symbol): List[String] =
      get(sym) match { case Some(entry) => entry.abbrevs case _ => Nil }


    /* recoding */

    private val (decoder, encoder) = {
      val mapping =
        for (entry <- entries; s <- entry.decode) yield entry.symbol -> s
      (new Recoder(mapping), new Recoder(for ((x, y) <- mapping) yield (y, x)))
    }

    def decode(text: String): String = decoder.recode(text)
    def encode(text: String): String = encoder.recode(text)

    private def recode_set(elems: Iterable[String]): Set[String] =
      (elems.iterator ++ elems.iterator.map(decode)).toSet

    private def recode_map[A](elems: Iterable[(String, A)]): Map[String, A] =
      (elems.iterator ++ elems.iterator.map({ case (sym, a) => (decode(sym), a) })).toMap


    /* user fonts */

    val fonts: Map[Symbol, String] =
      recode_map(for (entry <- entries; font <- entry.font) yield entry.symbol -> font)

    val font_names: List[String] = fonts.iterator.map(_._2).toSet.toList
    val font_index: Map[String, Int] = (font_names zip font_names.indices.toList).toMap

    def lookup_font(sym: Symbol): Option[Int] = fonts.get(sym).map(font_index(_))


    /* classification */

    val letters: Set[String] = recode_set(List(
      "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M",
      "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z",
      "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
      "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z",

      "\\<A>", "\\<B>", "\\<C>", "\\<D>", "\\<E>", "\\<F>", "\\<G>",
      "\\<H>", "\\<I>", "\\<J>", "\\<K>", "\\<L>", "\\<M>", "\\<N>",
      "\\<O>", "\\<P>", "\\<Q>", "\\<R>", "\\<S>", "\\<T>", "\\<U>",
      "\\<V>", "\\<W>", "\\<X>", "\\<Y>", "\\<Z>", "\\<a>", "\\<b>",
      "\\<c>", "\\<d>", "\\<e>", "\\<f>", "\\<g>", "\\<h>", "\\<i>",
      "\\<j>", "\\<k>", "\\<l>", "\\<m>", "\\<n>", "\\<o>", "\\<p>",
      "\\<q>", "\\<r>", "\\<s>", "\\<t>", "\\<u>", "\\<v>", "\\<w>",
      "\\<x>", "\\<y>", "\\<z>",

      "\\<AA>", "\\<BB>", "\\<CC>", "\\<DD>", "\\<EE>", "\\<FF>",
      "\\<GG>", "\\<HH>", "\\<II>", "\\<JJ>", "\\<KK>", "\\<LL>",
      "\\<MM>", "\\<NN>", "\\<OO>", "\\<PP>", "\\<QQ>", "\\<RR>",
      "\\<SS>", "\\<TT>", "\\<UU>", "\\<VV>", "\\<WW>", "\\<XX>",
      "\\<YY>", "\\<ZZ>", "\\<aa>", "\\<bb>", "\\<cc>", "\\<dd>",
      "\\<ee>", "\\<ff>", "\\<gg>", "\\<hh>", "\\<ii>", "\\<jj>",
      "\\<kk>", "\\<ll>", "\\<mm>", "\\<nn>", "\\<oo>", "\\<pp>",
      "\\<qq>", "\\<rr>", "\\<ss>", "\\<tt>", "\\<uu>", "\\<vv>",
      "\\<ww>", "\\<xx>", "\\<yy>", "\\<zz>",

      "\\<alpha>", "\\<beta>", "\\<gamma>", "\\<delta>", "\\<epsilon>",
      "\\<zeta>", "\\<eta>", "\\<theta>", "\\<iota>", "\\<kappa>",
      "\\<mu>", "\\<nu>", "\\<xi>", "\\<pi>", "\\<rho>", "\\<sigma>",
      "\\<tau>", "\\<upsilon>", "\\<phi>", "\\<chi>", "\\<psi>",
      "\\<omega>", "\\<Gamma>", "\\<Delta>", "\\<Theta>", "\\<Lambda>",
      "\\<Xi>", "\\<Pi>", "\\<Sigma>", "\\<Upsilon>", "\\<Phi>",
      "\\<Psi>", "\\<Omega>"))

    val blanks: Set[String] = recode_set(List(space, "\t", "\n", "\u000B", "\f", "\r", "\r\n"))

    val sym_chars =
      Set("!", "#", "$", "%", "&", "*", "+", "-", "/", "<", "=", ">", "?", "@", "^", "_", "|", "~")

    val symbolic: Set[String] =
      recode_set(for (entry <- entries if raw_symbolic(entry.symbol)) yield entry.symbol)


    /* misc symbols */

    val newline_decoded: Symbol = decode(newline)
    val comment_decoded: Symbol = decode(comment)
    val cancel_decoded: Symbol = decode(cancel)
    val latex_decoded: Symbol = decode(latex)
    val marker_decoded: Symbol = decode(marker)
    val open_decoded: Symbol = decode(open)
    val close_decoded: Symbol = decode(close)


    /* control symbols */

    val control_decoded: Set[Symbol] =
      (for (entry <- entries.iterator if entry.symbol.startsWith("\\<^"); s <- entry.decode)
        yield s).toSet

    val sub_decoded: Symbol = decode(sub)
    val sup_decoded: Symbol = decode(sup)
    val bold_decoded: Symbol = decode(bold)
    val emph_decoded: Symbol = decode(emph)
    val bsub_decoded: Symbol = decode(bsub)
    val esub_decoded: Symbol = decode(esub)
    val bsup_decoded: Symbol = decode(bsup)
    val esup_decoded: Symbol = decode(esup)
  }


  /* tables */

  def decode(text: String): String = symbols.decode(text)
  def encode(text: String): String = symbols.encode(text)

  def decode_yxml(text: String, cache: XML.Cache = XML.Cache.none): XML.Body =
    YXML.parse_body(decode(text), cache = cache)

  def decode_yxml_failsafe(text: String, cache: XML.Cache = XML.Cache.none): XML.Body =
    YXML.parse_body_failsafe(decode(text), cache = cache)

  def encode_yxml(body: XML.Body): String =
    YXML.string_of_body(body, recode = encode)

  def decode_strict(text: String): String = {
    val decoded = decode(text)
    if (encode(decoded) == text) decoded
    else {
      val bad = new mutable.ListBuffer[Symbol]
      for (s <- iterator(text) if encode(decode(s)) != s && !bad.contains(s)) bad += s
      error("Bad Unicode symbols in text: " + commas_quote(bad))
    }
  }

  def output(unicode_symbols: Boolean, text: String): String =
    if (unicode_symbols) Symbol.decode(text) else Symbol.encode(text)


  /* classification */

  def is_letter(sym: Symbol): Boolean = symbols.letters.contains(sym)
  def is_digit(sym: Symbol): Boolean = sym.length == 1 && '0' <= sym(0) && sym(0) <= '9'
  def is_quasi(sym: Symbol): Boolean = sym == "_" || sym == "'"
  def is_letdig(sym: Symbol): Boolean = is_letter(sym) || is_digit(sym) || is_quasi(sym)
  def is_blank(sym: Symbol): Boolean = symbols.blanks.contains(sym)


  /* symbolic newline */

  val newline: Symbol = "\\<newline>"
  def newline_decoded: Symbol = symbols.newline_decoded

  def print_newlines(str: String): String =
    if (str.contains('\n'))
      (for (s <- iterator(str)) yield { if (s == "\n") newline_decoded else s }).mkString
    else str


  /* formal comments */

  val comment: Symbol = "\\<comment>"
  val cancel: Symbol = "\\<^cancel>"
  val latex: Symbol = "\\<^latex>"
  val marker: Symbol = "\\<^marker>"

  def comment_decoded: Symbol = symbols.comment_decoded
  def cancel_decoded: Symbol = symbols.cancel_decoded
  def latex_decoded: Symbol = symbols.latex_decoded
  def marker_decoded: Symbol = symbols.marker_decoded


  /* cartouches */

  val open: Symbol = "\\<open>"
  val close: Symbol = "\\<close>"

  def open_decoded: Symbol = symbols.open_decoded
  def close_decoded: Symbol = symbols.close_decoded

  def is_open(sym: Symbol): Boolean = sym == open_decoded || sym == open
  def is_close(sym: Symbol): Boolean = sym == close_decoded || sym == close

  def cartouche(s: String): String = open + s + close
  def cartouche_decoded(s: String): String = open_decoded + s + close_decoded


  /* symbols for symbolic identifiers */

  private def raw_symbolic(sym: Symbol): Boolean =
    sym.startsWith("\\<") && sym.endsWith(">") && !sym.startsWith("\\<^")

  def is_symbolic(sym: Symbol): Boolean =
    !is_open(sym) && !is_close(sym) && (raw_symbolic(sym) || symbols.symbolic.contains(sym))

  def is_symbolic_char(sym: Symbol): Boolean = symbols.sym_chars.contains(sym)


  /* control symbols */

  val control_prefix = "\\<^"
  val control_suffix = ">"

  def control_name(sym: Symbol): Option[String] =
    if (is_control_encoded(sym))
      Some(sym.substring(control_prefix.length, sym.length - control_suffix.length))
    else None

  def is_control_encoded(sym: Symbol): Boolean =
    sym.startsWith(control_prefix) && sym.endsWith(control_suffix)

  def is_control(sym: Symbol): Boolean =
    is_control_encoded(sym) || symbols.control_decoded.contains(sym)

  def is_controllable(sym: Symbol): Boolean =
    !is_blank(sym) && !is_control(sym) && !is_open(sym) && !is_close(sym) &&
    !is_malformed(sym) && sym != "\""

  val sub: Symbol = "\\<^sub>"
  val sup: Symbol = "\\<^sup>"
  val bold: Symbol = "\\<^bold>"
  val emph: Symbol = "\\<^emph>"
  val bsub: Symbol = "\\<^bsub>"
  val esub: Symbol = "\\<^esub>"
  val bsup: Symbol = "\\<^bsup>"
  val esup: Symbol = "\\<^esup>"

  def sub_decoded: Symbol = symbols.sub_decoded
  def sup_decoded: Symbol = symbols.sup_decoded
  def bold_decoded: Symbol = symbols.bold_decoded
  def emph_decoded: Symbol = symbols.emph_decoded
  def bsub_decoded: Symbol = symbols.bsub_decoded
  def esub_decoded: Symbol = symbols.esub_decoded
  def bsup_decoded: Symbol = symbols.bsup_decoded
  def esup_decoded: Symbol = symbols.esup_decoded


  /* metric */

  def is_printable(sym: Symbol): Boolean =
    if (is_ascii(sym)) is_ascii_printable(sym(0))
    else !is_control(sym)

  object Metric extends Pretty.Metric {
    val unit = 1.0
    def apply(str: String): Double =
      (for (s <- iterator(str)) yield {
        val sym = encode(s)
        if (sym.startsWith("\\<long") || sym.startsWith("\\<Long")) 2
        else if (is_printable(sym)) 1
        else 0
      }).sum
  }
}
