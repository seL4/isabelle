/*  Title:      Pure/Thy/thy_syntax.scala
    Author:     Makarius

Superficial theory syntax: command spans.
*/

package isabelle


import scala.collection.mutable


object Thy_Syntax
{
  type Span = List[Token]

  def parse_spans(toks: List[Token]): List[Span] =
  {
    val result = new mutable.ListBuffer[Span]
    val span = new mutable.ListBuffer[Token]
    val whitespace = new mutable.ListBuffer[Token]

    def flush(buffer: mutable.ListBuffer[Token])
    {
      if (!buffer.isEmpty) { result += buffer.toList; buffer.clear }
    }
    for (tok <- toks) {
      if (tok.is_command) { flush(span); flush(whitespace); span += tok }
      else if (tok.is_ignored) whitespace += tok
      else { span ++= whitespace; whitespace.clear; span += tok }
    }
    flush(span); flush(whitespace)
    result.toList
  }
}
