/*  Title:      Pure/General/symbol.scala
    ID:         $Id$
    Author:     Makarius

Basic support for Isabelle symbols.
*/

package isabelle

import java.util.regex.Pattern


object Symbol {

  /* Regular expressions */

  private def compile(s: String) =
    Pattern.compile(s, Pattern.COMMENTS | Pattern.DOTALL)

  private val symbol_src = """ \\ \\? < (?:
      \^? [A-Za-z][A-Za-z0-9_']* |
      \^raw: [\x20-\x7e\u0100-\uffff && [^.>]]* ) >"""

  private val bad_symbol_src = "(?!" + symbol_src + ")" +
    """ \\ \\? < (?: (?! \p{Space} | [\"`\\] | \(\* | \*\) | \{\* | \*\} ) . )*"""

  val symbol_pattern = compile(symbol_src)
  val bad_symbol_pattern = compile(bad_symbol_src)
  val pattern = compile(symbol_src + "|" + bad_symbol_src + "| .")
}
