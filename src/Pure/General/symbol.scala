/*  Title:      Pure/General/symbol.scala
    ID:         $Id$
    Author:     Makarius

Basic support for Isabelle symbols.
*/

package isabelle

import java.util.regex.Pattern
import java.io.File
import scala.io.Source
import scala.collection.mutable.HashMap


object Symbol {

  /* Regexp utils */

  private def compile(s: String) =
    Pattern.compile(s, Pattern.COMMENTS | Pattern.DOTALL)


  /* Symbol regexps */

  private val symbol_src = """ \\ \\? < (?:
      \^? [A-Za-z][A-Za-z0-9_']* |
      \^raw: [\x20-\x7e\u0100-\uffff && [^.>]]* ) >"""

  private val bad_symbol_src = "(?!" + symbol_src + ")" +
    """ \\ \\? < (?: (?! \s | [\"`\\] | \(\* | \*\) | \{\* | \*\} ) . )*"""

  val symbol_pattern = compile(symbol_src)
  val bad_symbol_pattern = compile(bad_symbol_src)
  val pattern = compile(symbol_src + "|" + bad_symbol_src + "| .")


  /* Symbol interpretation tables */

  private val empty_pattern = compile(""" ^\s* (?: \#.* )? $ """)
  private val blank_pattern = compile(""" \s+ """)
  private val key_pattern = compile(""" (.+): """)

  class Interpretation extends HashMap[String, List[(String, String)]] {

    class BadEntry(val line: String) extends Exception

    def read_line(line: String) = {
      def err() = throw new BadEntry ("Bad symbol specification: " + line)

      def read_pairs(props: List[String]): List[(String, String)] = {
        props match {
          case Nil => Nil
          case _ :: Nil => err()
          case key :: value :: rest => {
            val key_matcher = key_pattern.matcher(key)
            if (key_matcher.matches) { (key_matcher.group(1) -> value) :: read_pairs(rest) }
            else err ()
          }
        }
      }

      if (!empty_pattern.matcher(line).matches) {
        blank_pattern.split(line).toList match {
          case Nil => err()
          case symbol :: props => this + (symbol -> read_pairs(props))
        }
      }
    }

    for (base <- List(IsabelleSystem.ISABELLE_HOME, IsabelleSystem.ISABELLE_HOME_USER)) {
      val file = new File(base + File.separator + "etc" + File.separator + "symbols")
      if (file.canRead) {
        for (line <- Source.fromFile(file).getLines) read_line(line)
      }
    }
  }

}
