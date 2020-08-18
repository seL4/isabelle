/*  Title:      HOL/Tools/Nitpick/kodkod.scala
    Author:     Makarius

Scala interface for Kodkod.
*/

package isabelle.nitpick

import isabelle._

import org.antlr.runtime.{ANTLRInputStream, Lexer, RecognitionException}
import de.tum.in.isabelle.Kodkodi.{KodkodiLexer, KodkodiParser}


object Kodkod
{
  def kodkod(source: String,
    solve_all: Boolean = false,
    prove: Boolean = false,
    max_solutions: Int = Integer.MAX_VALUE,
    cleanup_inst: Boolean = false,
    time_limit: Time = Time.zero,
    max_threads: Int = 1): String =
  {
    val in = Bytes(source).stream
    val stream = new ANTLRInputStream(in)
    val lexer = new KodkodiLexer(stream)

    val parser =
      KodkodiParser.create(true, false, solve_all, prove, max_solutions,
        cleanup_inst, max_threads, lexer)

    "FIXME"
  }
}
