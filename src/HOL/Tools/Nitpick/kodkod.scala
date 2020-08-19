/*  Title:      HOL/Tools/Nitpick/kodkod.scala
    Author:     Makarius

Scala interface for Kodkod.
*/

package isabelle.nitpick

import isabelle._

import java.util.concurrent.Executors

import org.antlr.runtime.{ANTLRInputStream, Lexer, RecognitionException}
import de.tum.in.isabelle.Kodkodi.{Context, KodkodiLexer, KodkodiParser}


object Kodkod
{
  def kodkod(source: String,
    solve_all: Boolean = false,
    prove: Boolean = false,
    max_solutions: Int = Integer.MAX_VALUE,
    cleanup_inst: Boolean = false,
    max_threads: Int = 1): String =
  {
    val context =
      new Context {
        private val out = new StringBuilder
        private val err = new StringBuilder
        def result: (String, String) = synchronized { (out.toString, err.toString) }
        override def output(s: String): Unit = synchronized { out ++= s; out += '\n' }
        override def error(s: String): Unit = synchronized { err ++= s; err += '\n' }
        override def exit(rc: Int) { if (rc == 0) () else error("exit " + rc) }
      }
    val executor = Executors.newFixedThreadPool(max_threads)
    val lexer = new KodkodiLexer(new ANTLRInputStream(Bytes(source).stream))
    val parser =
      KodkodiParser.create(context, executor,
        false, solve_all, prove, max_solutions, cleanup_inst, lexer)

    val solution =
        try { parser.problems() }
        catch {
          case exn: RecognitionException =>
            parser.reportError(exn)
            error("Parser error")
        }
    if (parser.getTokenStream.LA(1) != KodkodiParser.EOF) {
      error("Trailing tokens")
    }
    if (lexer.getNumberOfSyntaxErrors > 0) error("Lexical error")
    if (parser.getNumberOfSyntaxErrors > 0) error("Syntax error")

    val (out, err) = context.result
    Output.writeln(out)
    Output.warning(err)

    solution
  }
}
