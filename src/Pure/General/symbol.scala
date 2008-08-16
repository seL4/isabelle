/*  Title:      Pure/General/symbol.scala
    ID:         $Id$
    Author:     Makarius

Detecting and recoding Isabelle symbols.
*/

package isabelle

import java.util.regex.{Pattern, Matcher}
import java.io.File
import scala.io.Source
import scala.collection.jcl.HashMap


object Symbol {

  /** Symbol regexps **/

  private def compile(s: String) =
    Pattern.compile(s, Pattern.COMMENTS | Pattern.DOTALL)

  val char_pattern = compile(""" [^\ud800-\udfff] | [\ud800-\udbff][\udc00-\udfff] """)

  val symbol_pattern = compile(""" \\ \\? < (?:
      \^? [A-Za-z][A-Za-z0-9_']* |
      \^raw: [\x20-\x7e\u0100-\uffff && [^.>]]* ) >""")

  val bad_symbol_pattern = compile("(?!" + symbol_pattern + ")" +
    """ \\ \\? < (?: (?! \s | [\"`\\] | \(\* | \*\) | \{\* | \*\} ) . )*""")

  val pattern = compile(char_pattern + "|" + symbol_pattern + "|" + bad_symbol_pattern)



  /** Recoder tables **/

  class Recoder(list: List[(String, String)]) {
    var pattern: Pattern = null
    var table = new HashMap[String, String]

    def recode(text: String) = {
      val output = new StringBuffer(text.length)
      val matcher = pattern.matcher(text)
      while(matcher.find) matcher.appendReplacement(output, table(matcher.group))
      matcher.appendTail(output)
      output.toString
    }

    /* constructor */
    {
      val pat = new StringBuilder(500)
      val elems = list.elements
      for ((x, y) <- elems) {
        pat.append(Pattern.quote(x))
        if (elems.hasNext) pat.append("|")
        table + (x -> Matcher.quoteReplacement(y))
      }
      pattern = compile(pat.toString)
    }
  }



  /** Symbol interpretation **/

  class Interpretation {

    class BadSymbol(val msg: String) extends Exception

    private var symbols = new HashMap[String, HashMap[String, String]]
    var decoder: Recoder = null
    var encoder: Recoder = null

    def decode(text: String) = decoder.recode(text)
    def encode(text: String) = encoder.recode(text)


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

    private def get_code(entry: (String, HashMap[String, String])) = {
      val (symbol, props) = entry
      val code =
        try { Integer.decode(props("code")).intValue }
        catch {
          case e: NoSuchElementException => throw new BadSymbol(symbol)
          case e: NumberFormatException => throw new BadSymbol(symbol)
        }
      (symbol, new String(Character.toChars(code)))
    }

    private def init_recoders() = {
      val list = symbols.elements.toList.map(get_code)
      decoder = new Recoder(list)
      encoder = new Recoder(list.map((p: (String, String)) => (p._2, p._1)))
    }


    /* constructor */

    read_symbols(IsabelleSystem.ISABELLE_HOME)
    read_symbols(IsabelleSystem.ISABELLE_HOME_USER)
    init_recoders()
  }

}
