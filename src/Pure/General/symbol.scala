/*  Title:      Pure/General/symbol.scala
    ID:         $Id$
    Author:     Makarius

Detecting and recoding Isabelle symbols.
*/

package isabelle

import java.util.regex.Pattern
import java.io.File
import scala.io.Source
import scala.collection.jcl.HashMap


object Symbol {

  /** Symbol regexps **/

  private def compile(s: String) =
    Pattern.compile(s, Pattern.COMMENTS | Pattern.DOTALL)

  private val plain_pattern = compile(""" [^\\ \ud800-\udfff] | [\ud800-\udbff][\udc00-\udfff] """)

  private val symbol_pattern = compile(""" \\ \\? < (?:
      \^? [A-Za-z][A-Za-z0-9_']* |
      \^raw: [\x20-\x7e\u0100-\uffff && [^.>]]* ) >""")

  private val bad_symbol_pattern = compile("(?!" + symbol_pattern + ")" +
    """ \\ \\? < (?: (?! \s | [\"`\\] | \(\* | \*\) | \{\* | \*\} ) . )*""")

  // total pattern
  val pattern = compile(plain_pattern + "|" + symbol_pattern + "|" + bad_symbol_pattern + "| .")



  /** Recoding **/

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
      val table = new HashMap[String, String]
      for ((x, y) <- list) table + (x -> y)
      table
    }
    def recode(text: String) = {
      val len = text.length
      val matcher = pattern.matcher(text)
      val result = new StringBuilder(len)
      var i = 0
      while (i < len) {
        val c = text(i)
        if (min <= c && c <= max) {
          matcher.region(i, len)
          matcher.lookingAt
          val x = matcher.group
          table.get(x) match {
            case Some(y) => result.append(y)
            case None => result.append(x)
          }
          i = matcher.end
        }
        else { result.append(c); i += 1 }
      }
      result.toString
    }
  }



  /** Symbol interpretation **/

  class Interpretation {

    private var symbols = new HashMap[String, HashMap[String, String]]
    private var decoder: Recoder = null
    private var encoder: Recoder = null

    def decode(text: String) = decoder.recode(text)
    def encode(text: String) = encoder.recode(text)


    /* read symbols */

    private val empty_pattern = compile(""" ^\s* (?: \#.* )? $ """)
    private val blank_pattern = compile(""" \s+ """)
    private val key_pattern = compile(""" (.+): """)

    private def read_line(line: String) = {
      def err() = error("Bad symbol specification (line " + line + ")")

      def read_props(props: List[String], tab: HashMap[String, String]): Unit = {
        props match {
          case Nil => ()
          case _ :: Nil => err()
          case key :: value :: rest => {
            val key_matcher = key_pattern.matcher(key)
            if (key_matcher.matches) {
              tab + (key_matcher.group(1) -> value)
              read_props(rest, tab)
            }
            else err ()
          }
        }
      }

      if (!empty_pattern.matcher(line).matches) {
        blank_pattern.split(line).toList match {
          case Nil => err()
          case symbol :: props => {
            val tab = new HashMap[String, String]
            read_props(props, tab)
            symbols + (symbol -> tab)
          }
        }
      }
    }

    private def read_symbols(path: String) = {
      val file = new File(IsabelleSystem.platform_path(path))
      if (file.canRead) {
        for (line <- Source.fromFile(file).getLines) read_line(line)
      }
    }


    /* init tables */

    private def get_code(entry: (String, HashMap[String, String])) = {
      val (symbol, props) = entry
      val code =
        try { Integer.decode(props("code")).intValue }
        catch {
          case _: NoSuchElementException => error("Missing code for symbol " + symbol)
          case _: NumberFormatException => error("Bad code for symbol " + symbol)
        }
      (symbol, new String(Character.toChars(code)))
    }

    private def init_recoders() = {
      val list = symbols.elements.toList.map(get_code)
      decoder = new Recoder(list ++ (for ((x, y) <- list) yield ("\\" + x, y)))
      encoder = new Recoder(for ((x, y) <- list) yield (y, x))
    }


    /* constructor */

    read_symbols("$ISABELLE_HOME/etc/symbols")
    read_symbols("$ISABELLE_HOME_USER/etc/symbols")
    init_recoders()
  }

}
