/*  Title:      Pure/General/symbol.scala
    Author:     Makarius

Detecting and recoding Isabelle symbols.
*/

package isabelle

import scala.io.Source
import scala.collection.mutable
import scala.util.matching.Regex


object Symbol
{
  /* spaces */

  val spc = ' '
  val space = " "

  private val static_spaces = space * 4000

  def spaces(k: Int): String =
  {
    require(k >= 0)
    if (k < static_spaces.length) static_spaces.substring(0, k)
    else space * k
  }


  /* ASCII characters */

  def is_ascii_letter(c: Char): Boolean = 'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z'
  def is_ascii_digit(c: Char): Boolean = '0' <= c && c <= '9'
  def is_ascii_quasi(c: Char): Boolean = c == '_' || c == '\''

  def is_ascii_letdig(c: Char): Boolean =
    is_ascii_letter(c) || is_ascii_digit(c) || is_ascii_quasi(c)

  def is_ascii_identifier(s: String): Boolean =
    s.length > 0 && is_ascii_letter(s(0)) && s.substring(1).forall(is_ascii_letdig)


  /* Symbol regexps */

  private val plain = new Regex("""(?xs)
      [^\r\\\ud800-\udfff\ufffd] | [\ud800-\udbff][\udc00-\udfff] """)

  private val physical_newline = new Regex("""(?xs) \n | \r\n | \r """)

  private val symbol = new Regex("""(?xs)
      \\ < (?:
      \^? [A-Za-z][A-Za-z0-9_']* |
      \^raw: [\x20-\x7e\u0100-\uffff && [^.>]]* ) >""")

  private val malformed_symbol = new Regex("(?xs) (?!" + symbol + ")" +
    """ [\ud800-\udbff\ufffd] | \\<\^? """)

  val regex_total =
    new Regex(plain + "|" + physical_newline + "|" + symbol + "|" + malformed_symbol + "| .")


  /* basic matching */

  def is_plain(c: Char): Boolean = !(c == '\r' || c == '\\' || '\ud800' <= c && c <= '\udfff')

  def is_physical_newline(s: String): Boolean =
    s == "\n" || s == "\r" || s == "\r\n"

  def is_malformed(s: String): Boolean =
    !(s.length == 1 && is_plain(s(0))) && malformed_symbol.pattern.matcher(s).matches

  class Matcher(text: CharSequence)
  {
    private val matcher = regex_total.pattern.matcher(text)
    def apply(start: Int, end: Int): Int =
    {
      require(0 <= start && start < end && end <= text.length)
      if (is_plain(text.charAt(start))) 1
      else {
        matcher.region(start, end).lookingAt
        matcher.group.length
      }
    }
  }


  /* iterator */

  private val char_symbols: Array[String] =
    (0 until 256).iterator.map(i => new String(Array(i.toChar))).toArray

  def iterator(text: CharSequence): Iterator[String] =
    new Iterator[String]
    {
      private val matcher = new Matcher(text)
      private var i = 0
      def hasNext = i < text.length
      def next =
      {
        val n = matcher(i, text.length)
        val s =
          if (n == 0) ""
          else if (n == 1) {
            val c = text.charAt(i)
            if (c < char_symbols.length) char_symbols(c)
            else text.subSequence(i, i + n).toString
          }
          else text.subSequence(i, i + n).toString
        i += n
        s
      }
    }


  /* decoding offsets */

  class Index(text: CharSequence)
  {
    case class Entry(chr: Int, sym: Int)
    val index: Array[Entry] =
    {
      val matcher = new Matcher(text)
      val buf = new mutable.ArrayBuffer[Entry]
      var chr = 0
      var sym = 0
      while (chr < text.length) {
        val n = matcher(chr, text.length)
        chr += n
        sym += 1
        if (n > 1) buf += Entry(chr, sym)
      }
      buf.toArray
    }
    def decode(sym1: Int): Int =
    {
      val sym = sym1 - 1
      val end = index.length
      def bisect(a: Int, b: Int): Int =
      {
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
    def decode(range: Text.Range): Text.Range = range.map(decode(_))
  }


  /* recoding text */

  private class Recoder(list: List[(String, String)])
  {
    private val (min, max) =
    {
      var min = '\uffff'
      var max = '\u0000'
      for ((x, _) <- list) {
        val c = x(0)
        if (c < min) min = c
        if (c > max) max = c
      }
      (min, max)
    }
    private val table =
    {
      var tab = Map[String, String]()
      for ((x, y) <- list) {
        tab.get(x) match {
          case None => tab += (x -> y)
          case Some(z) =>
            error("Duplicate mapping of \"" + x + "\" to \"" + y + "\" vs. \"" + z + "\"")
        }
      }
      tab
    }
    def recode(text: String): String =
    {
      val len = text.length
      val matcher = regex_total.pattern.matcher(text)
      val result = new StringBuilder(len)
      var i = 0
      while (i < len) {
        val c = text(i)
        if (min <= c && c <= max) {
          matcher.region(i, len).lookingAt
          val x = matcher.group
          result.append(table.get(x) getOrElse x)
          i = matcher.end
        }
        else { result.append(c); i += 1 }
      }
      result.toString
    }
  }



  /** symbol interpretation **/

  private lazy val symbols =
    new Interpretation(
      Isabelle_System.try_read(Path.split(Isabelle_System.getenv_strict("ISABELLE_SYMBOLS"))))

  private class Interpretation(symbols_spec: String)
  {
    /* read symbols */

    private val empty = new Regex("""(?xs) ^\s* (?: \#.* )? $ """)
    private val key = new Regex("""(?xs) (.+): """)

    private def read_decl(decl: String): (String, Map[String, String]) =
    {
      def err() = error("Bad symbol declaration: " + decl)

      def read_props(props: List[String]): Map[String, String] =
      {
        props match {
          case Nil => Map()
          case _ :: Nil => err()
          case key(x) :: y :: rest => read_props(rest) + (x -> y)
          case _ => err()
        }
      }
      decl.split("\\s+").toList match {
        case sym :: props if sym.length > 1 && !is_malformed(sym) => (sym, read_props(props))
        case _ => err()
      }
    }

    private val symbols: List[(String, Map[String, String])] =
      Map((
        for (decl <- split_lines(symbols_spec) if !empty.pattern.matcher(decl).matches)
          yield read_decl(decl)): _*) toList


    /* misc properties */

    val names: Map[String, String] =
    {
      val name = new Regex("""\\<\^?([A-Za-z][A-Za-z0-9_']*)>""")
      Map((for ((sym @ name(a), _) <- symbols) yield (sym -> a)): _*)
    }

    val abbrevs: Map[String, String] =
      Map((
        for ((sym, props) <- symbols if props.isDefinedAt("abbrev"))
          yield (sym -> props("abbrev"))): _*)


    /* recoding */

    private val (decoder, encoder) =
    {
      val mapping =
        for {
          (sym, props) <- symbols
          val code =
            try { Integer.decode(props("code")).intValue }
            catch {
              case _: NoSuchElementException => error("Missing code for symbol " + sym)
              case _: NumberFormatException => error("Bad code for symbol " + sym)
            }
          val ch = new String(Character.toChars(code))
        } yield {
          if (code < 128) error("Illegal ASCII code for symbol " + sym)
          else (sym, ch)
        }
      (new Recoder(mapping),
       new Recoder(mapping map { case (x, y) => (y, x) }))
    }

    def decode(text: String): String = decoder.recode(text)
    def encode(text: String): String = encoder.recode(text)

    private def recode_set(elems: String*): Set[String] =
    {
      val content = elems.toList
      Set((content ::: content.map(decode)): _*)
    }

    private def recode_map[A](elems: (String, A)*): Map[String, A] =
    {
      val content = elems.toList
      Map((content ::: content.map({ case (sym, a) => (decode(sym), a) })): _*)
    }


    /* user fonts */

    val fonts: Map[String, String] =
      recode_map((
        for ((sym, props) <- symbols if props.isDefinedAt("font"))
          yield (sym -> props("font"))): _*)

    val font_names: List[String] = Set(fonts.toList.map(_._2): _*).toList
    val font_index: Map[String, Int] = Map((font_names zip (0 until font_names.length).toList): _*)


    /* classification */

    val letters = recode_set(
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
      "\\<Psi>", "\\<Omega>",

      "\\<^isub>", "\\<^isup>")

    val blanks =
      recode_set(space, "\t", "\n", "\u000B", "\f", "\r", "\\<spacespace>", "\\<^newline>")

    val sym_chars =
      Set("!", "#", "$", "%", "&", "*", "+", "-", "/", "<", "=", ">", "?", "@", "^", "_", "|", "~")


    /* control symbols */

    val ctrl_decoded: Set[String] =
      Set((for ((sym, _) <- symbols if sym.startsWith("\\<^")) yield decode(sym)): _*)

    val subscript_decoded = Set(decode("\\<^sub>"), decode("\\<^isub>"))
    val superscript_decoded = Set(decode("\\<^sup>"), decode("\\<^isup>"))

    val bold_decoded = decode("\\<^bold>")
    val bsub_decoded = decode("\\<^bsub>")
    val esub_decoded = decode("\\<^esub>")
    val bsup_decoded = decode("\\<^bsup>")
    val esup_decoded = decode("\\<^esup>")
  }


  /* tables */

  def names: Map[String, String] = symbols.names
  def abbrevs: Map[String, String] = symbols.abbrevs

  def decode(text: String): String = symbols.decode(text)
  def encode(text: String): String = symbols.encode(text)

  def fonts: Map[String, String] = symbols.fonts
  def font_names: List[String] = symbols.font_names
  def font_index: Map[String, Int] = symbols.font_index
  def lookup_font(sym: String): Option[Int] = symbols.fonts.get(sym).map(font_index(_))


  /* classification */

  def is_letter(sym: String): Boolean = symbols.letters.contains(sym)
  def is_digit(sym: String): Boolean = sym.length == 1 && '0' <= sym(0) && sym(0) <= '9'
  def is_quasi(sym: String): Boolean = sym == "_" || sym == "'"
  def is_letdig(sym: String): Boolean = is_letter(sym) || is_digit(sym) || is_quasi(sym)
  def is_blank(sym: String): Boolean = symbols.blanks.contains(sym)
  def is_symbolic_char(sym: String): Boolean = symbols.sym_chars.contains(sym)
  def is_symbolic(sym: String): Boolean =
    sym.startsWith("\\<") && sym.endsWith(">") && !sym.startsWith("\\<^")


  /* control symbols */

  def is_ctrl(sym: String): Boolean =
    sym.startsWith("\\<^") || symbols.ctrl_decoded.contains(sym)

  def is_controllable(sym: String): Boolean =
    !is_blank(sym) && !is_ctrl(sym) && !is_malformed(sym)

  def is_subscript_decoded(sym: String): Boolean = symbols.subscript_decoded.contains(sym)
  def is_superscript_decoded(sym: String): Boolean = symbols.superscript_decoded.contains(sym)
  def is_bold_decoded(sym: String): Boolean = sym == symbols.bold_decoded
  def is_bsub_decoded(sym: String): Boolean = sym == symbols.bsub_decoded
  def is_esub_decoded(sym: String): Boolean = sym == symbols.esub_decoded
  def is_bsup_decoded(sym: String): Boolean = sym == symbols.bsup_decoded
  def is_esup_decoded(sym: String): Boolean = sym == symbols.esup_decoded
}
