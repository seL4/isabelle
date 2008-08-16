/*  Title:      Pure/General/symbol.scala
    ID:         $Id$
    Author:     Makarius

Basic support for Isabelle symbols.
*/

package isabelle

import java.util.regex.Pattern
import java.io.File
import scala.io.Source
import scala.collection.jcl.HashMap


object Symbol {

  /** Regexp utils **/

  private def compile(s: String) =
    Pattern.compile(s, Pattern.COMMENTS | Pattern.DOTALL)



  /** Symbol regexps **/

  private val char_src = """ [^\ud800-\udfff] | [\ud800-\udbff][\udc00-\udfff] """

  private val symbol_src = """ \\ \\? < (?:
      \^? [A-Za-z][A-Za-z0-9_']* |
      \^raw: [\x20-\x7e\u0100-\uffff && [^.>]]* ) >"""

  private val bad_symbol_src = "(?!" + symbol_src + ")" +
    """ \\ \\? < (?: (?! \s | [\"`\\] | \(\* | \*\) | \{\* | \*\} ) . )*"""

  val char_pattern = compile(char_src)
  val symbol_pattern = compile(symbol_src)
  val bad_symbol_pattern = compile(bad_symbol_src)
  val pattern = compile(char_pattern + "|" + symbol_src + "|" + bad_symbol_src)



  /** Symbol interpretation **/

  class Interpretation {

    class BadSymbol(val msg: String) extends Exception

    var symbols = new HashMap[String, HashMap[String, String]]

    var decode_pattern: Pattern = null
    var decode_table = new HashMap[String, String]

    var encode_pattern: Pattern = null
    var encode_table = new HashMap[String, String]


    /* recode */

    private def recode(pattern: Pattern, table: HashMap[String, String], text: String) = {
      // FIXME
      text
    }

    def decode(text: String) = recode(decode_pattern, decode_table, text)
    def encode(text: String) = recode(encode_pattern, encode_table, text)


    /* read symbols */

    private val empty_pattern = compile(""" ^\s* (?: \#.* )? $ """)
    private val blank_pattern = compile(""" \s+ """)
    private val key_pattern = compile(""" (.+): """)

    private def read_line(line: String) = {
      def err() = throw new BadSymbol(line)

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

    private def read_symbols(base: String) = {
      val file = new File(base + File.separator + "etc" + File.separator + "symbols")
      if (file.canRead) {
        for (line <- Source.fromFile(file).getLines) read_line(line)
      }
    }


    /* init tables */

    private def init_tables() = {
      val decode_pat = new StringBuilder
      val encode_pat = new StringBuilder

      val syms = symbols.elements
      for ((symbol, props) <- syms) {
        val code = {
          try { Integer.decode(props("code")) }
          catch {
            case e: NoSuchElementException => throw new BadSymbol(symbol)
            case e: NumberFormatException => throw new BadSymbol(symbol)
          }
        }
        val code_str = new String(Character.toChars(code.intValue))

        decode_pat.append(Pattern.quote(symbol))
        encode_pat.append(Pattern.quote(code_str))
        if (syms.hasNext) {
          decode_pat.append("|")
          encode_pat.append("|")
        }

        decode_table + (symbol -> code_str)
        encode_table + (code_str -> symbol)
      }

      decode_pattern = compile(decode_pat.toString)
      encode_pattern = compile(encode_pat.toString)
    }


    /* constructor */

    read_symbols(IsabelleSystem.ISABELLE_HOME)
    read_symbols(IsabelleSystem.ISABELLE_HOME_USER)
    init_tables()
  }

}
