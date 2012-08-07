/*  Title:      Pure/General/symbol.scala
    Author:     Makarius

Detecting and recoding Isabelle symbols.
*/

package isabelle

import scala.collection.mutable
import scala.util.matching.Regex


object Symbol
{
  type Symbol = String


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

  def is_physical_newline(s: Symbol): Boolean =
    s == "\n" || s == "\r" || s == "\r\n"

  def is_malformed(s: Symbol): Boolean =
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

  private val char_symbols: Array[Symbol] =
    (0 until 256).iterator.map(i => new String(Array(i.toChar))).toArray

  def iterator(text: CharSequence): Iterator[Symbol] =
    new Iterator[Symbol]
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

  def explode(text: CharSequence): List[Symbol] = iterator(text).toList


  /* decoding offsets */

  class Index(text: CharSequence)
  {
    sealed case class Entry(chr: Int, sym: Int)
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
            error("Duplicate mapping of " + quote(x) + " to " + quote(y) + " vs. " + quote(z))
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
    new Interpretation(File.try_read(Path.split(Isabelle_System.getenv_strict("ISABELLE_SYMBOLS"))))

  private class Interpretation(symbols_spec: String)
  {
    /* read symbols */

    private val empty = new Regex("""(?xs) ^\s* (?: \#.* )? $ """)
    private val key = new Regex("""(?xs) (.+): """)

    private def read_decl(decl: String): (Symbol, Map[String, String]) =
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

    private val symbols: List[(Symbol, Map[String, String])] =
      Map((
        for (decl <- split_lines(symbols_spec) if !empty.pattern.matcher(decl).matches)
          yield read_decl(decl)): _*).toList


    /* misc properties */

    val names: Map[Symbol, String] =
    {
      val name = new Regex("""\\<\^?([A-Za-z][A-Za-z0-9_']*)>""")
      Map((for ((sym @ name(a), _) <- symbols) yield (sym -> a)): _*)
    }

    val abbrevs: Map[Symbol, String] =
      Map((
        for ((sym, props) <- symbols if props.isDefinedAt("abbrev"))
          yield (sym -> props("abbrev"))): _*)


    /* recoding */

    private val (decoder, encoder) =
    {
      val mapping =
        for {
          (sym, props) <- symbols
          code =
            try { Integer.decode(props("code")).intValue }
            catch {
              case _: NoSuchElementException => error("Missing code for symbol " + sym)
              case _: NumberFormatException => error("Bad code for symbol " + sym)
            }
          ch = new String(Character.toChars(code))
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

    val fonts: Map[Symbol, String] =
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
      recode_set(" ", "\t", "\n", "\u000B", "\f", "\r", "\r\n", "\\<spacespace>", "\\<^newline>")

    val sym_chars =
      Set("!", "#", "$", "%", "&", "*", "+", "-", "/", "<", "=", ">", "?", "@", "^", "_", "|", "~")

    val symbolic = recode_set((for { (sym, _) <- symbols; if raw_symbolic(sym) } yield sym): _*)


    /* control symbols */

    val ctrl_decoded: Set[Symbol] =
      Set((for ((sym, _) <- symbols if sym.startsWith("\\<^")) yield decode(sym)): _*)

    val sub_decoded = decode("\\<^sub>")
    val sup_decoded = decode("\\<^sup>")
    val isub_decoded = decode("\\<^isub>")
    val isup_decoded = decode("\\<^isup>")
    val bsub_decoded = decode("\\<^bsub>")
    val esub_decoded = decode("\\<^esub>")
    val bsup_decoded = decode("\\<^bsup>")
    val esup_decoded = decode("\\<^esup>")
    val bold_decoded = decode("\\<^bold>")
  }


  /* tables */

  def names: Map[Symbol, String] = symbols.names
  def abbrevs: Map[Symbol, String] = symbols.abbrevs

  def decode(text: String): String = symbols.decode(text)
  def encode(text: String): String = symbols.encode(text)

  def fonts: Map[Symbol, String] = symbols.fonts
  def font_names: List[String] = symbols.font_names
  def font_index: Map[String, Int] = symbols.font_index
  def lookup_font(sym: Symbol): Option[Int] = symbols.fonts.get(sym).map(font_index(_))


  /* classification */

  def is_letter(sym: Symbol): Boolean = symbols.letters.contains(sym)
  def is_digit(sym: Symbol): Boolean = sym.length == 1 && '0' <= sym(0) && sym(0) <= '9'
  def is_quasi(sym: Symbol): Boolean = sym == "_" || sym == "'"
  def is_letdig(sym: Symbol): Boolean = is_letter(sym) || is_digit(sym) || is_quasi(sym)
  def is_blank(sym: Symbol): Boolean = symbols.blanks.contains(sym)

  def is_symbolic_char(sym: Symbol): Boolean = symbols.sym_chars.contains(sym)
  def is_symbolic(sym: Symbol): Boolean = raw_symbolic(sym) || symbols.symbolic.contains(sym)

  private def raw_symbolic(sym: Symbol): Boolean =
    sym.startsWith("\\<") && sym.endsWith(">") && !sym.startsWith("\\<^")




  /* control symbols */

  def is_ctrl(sym: Symbol): Boolean =
    sym.startsWith("\\<^") || symbols.ctrl_decoded.contains(sym)

  def is_controllable(sym: Symbol): Boolean =
    !is_blank(sym) && !is_ctrl(sym) && !is_malformed(sym)

  def sub_decoded: Symbol = symbols.sub_decoded
  def sup_decoded: Symbol = symbols.sup_decoded
  def isub_decoded: Symbol = symbols.isub_decoded
  def isup_decoded: Symbol = symbols.isup_decoded
  def bsub_decoded: Symbol = symbols.bsub_decoded
  def esub_decoded: Symbol = symbols.esub_decoded
  def bsup_decoded: Symbol = symbols.bsup_decoded
  def esup_decoded: Symbol = symbols.esup_decoded
  def bold_decoded: Symbol = symbols.bold_decoded
}
