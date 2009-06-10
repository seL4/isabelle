/*  Title:      Pure/General/symbol.scala
    Author:     Makarius

Detecting and recoding Isabelle symbols.
*/

package isabelle

import scala.io.Source
import scala.collection.jcl
import scala.util.matching.Regex


object Symbol
{

  /** Symbol regexps **/

  private val plain = new Regex("""(?xs)
    [^\\ \ud800-\udfff] | [\ud800-\udbff][\udc00-\udfff] """)

  private val symbol = new Regex("""(?xs)
      \\ < (?:
      \^? [A-Za-z][A-Za-z0-9_']* |
      \^raw: [\x20-\x7e\u0100-\uffff && [^.>]]* ) >""")

  private val bad_symbol = new Regex("(?xs) (?!" + symbol + ")" +
    """ \\ < (?: (?! \s | [\"`\\] | \(\* | \*\) | \{\* | \*\} ) . )*""")

  // total pattern
  val regex = new Regex(plain + "|" + symbol + "|" + bad_symbol + "| .")

  // prefix of another symbol
  def is_open(s: String): Boolean =
  {
    val len = s.length
    len == 1 && Character.isHighSurrogate(s(0)) ||
    s == "\\" ||
    s == "\\<" ||
    len > 2 && s(len - 1) != '>'
  }


  /** Recoding **/

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
      val table = new jcl.HashMap[String, String]   // reasonably efficient?
      for ((x, y) <- list) table + (x -> y)
      table
    }
    def recode(text: String): String =
    {
      val len = text.length
      val matcher = regex.pattern.matcher(text)
      val result = new StringBuilder(len)
      var i = 0
      while (i < len) {
        val c = text(i)
        if (min <= c && c <= max) {
          matcher.region(i, len)
          matcher.lookingAt
          val x = matcher.group
          result.append(table.get(x) getOrElse x)
          i = matcher.end
        }
        else { result.append(c); i += 1 }
      }
      result.toString
    }
  }



  /** Symbol interpretation **/

  class Interpretation(symbol_decls: Iterator[String])
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
        case Nil => err()
        case sym :: props => (sym, read_props(props))
      }
    }

    private val symbols: List[(String, Map[String, String])] =
      for (decl <- symbol_decls.toList if !empty.pattern.matcher(decl).matches)
        yield read_decl(decl)


    /* main recoder methods */

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
        } yield (sym, ch)
      (new Recoder(mapping),
       new Recoder(for ((x, y) <- mapping) yield (y, x)))
    }

    def decode(text: String) = decoder.recode(text)
    def encode(text: String) = encoder.recode(text)

  }
}
