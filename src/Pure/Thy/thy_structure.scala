/*  Title:      Pure/Thy/thy_structure.scala
    Author:     Makarius

Nested structure of theory source.
*/

package isabelle


import scala.collection.mutable
import scala.annotation.tailrec


object Thy_Structure
{
  sealed abstract class Entry { def length: Int }
  case class Block(val name: String, val body: List[Entry]) extends Entry
  {
    val length: Int = (0 /: body)(_ + _.length)
  }
  case class Atom(val command: Command) extends Entry
  {
    def length: Int = command.length
  }

  def parse(syntax: Outer_Syntax, node_name: Document.Node.Name, text: CharSequence): Entry =
  {
    /* stack operations */

    def buffer(): mutable.ListBuffer[Entry] = new mutable.ListBuffer[Entry]
    var stack: List[(Int, String, mutable.ListBuffer[Entry])] =
      List((0, node_name.toString, buffer()))

    @tailrec def close(level: Int => Boolean)
    {
      stack match {
        case (lev, name, body) :: (_, _, body2) :: rest if level(lev) =>
          body2 += Block(name, body.toList)
          stack = stack.tail
          close(level)
        case _ =>
      }
    }

    def result(): Entry =
    {
      close(_ => true)
      val (_, name, body) = stack.head
      Block(name, body.toList)
    }

    def add(command: Command)
    {
      syntax.heading_level(command) match {
        case Some(i) =>
          close(_ > i)
          stack = (i + 1, command.source, buffer()) :: stack
        case None =>
      }
      stack.head._3 += Atom(command)
    }


    /* result structure */

    val spans = syntax.parse_spans(syntax.scan(text))
    spans.foreach(span => add(Command(Document_ID.none, node_name, Nil, span)))
    result()
  }
}

