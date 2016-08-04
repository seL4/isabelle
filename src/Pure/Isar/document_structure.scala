/*  Title:      Pure/Isar/document_structure.scala
    Author:     Makarius

Overall document structure.
*/

package isabelle


import scala.collection.mutable
import scala.annotation.tailrec


object Document_Structure
{
  /* general structure */

  sealed abstract class Document { def length: Int }
  case class Block(name: String, text: String, body: List[Document]) extends Document
  { val length: Int = (0 /: body)(_ + _.length) }
  case class Atom(command: Command) extends Document
  { def length: Int = command.length }


  /* section headings etc. */

  def heading_level(keywords: Keyword.Keywords, command: Command): Option[Int] =
  {
    val name = command.span.name
    name match {
      case Thy_Header.CHAPTER => Some(0)
      case Thy_Header.SECTION => Some(1)
      case Thy_Header.SUBSECTION => Some(2)
      case Thy_Header.SUBSUBSECTION => Some(3)
      case Thy_Header.PARAGRAPH => Some(4)
      case Thy_Header.SUBPARAGRAPH => Some(5)
      case _ =>
        keywords.kinds.get(name) match {
          case Some(kind) if Keyword.theory(kind) && !Keyword.theory_end(kind) => Some(6)
          case _ => None
        }
    }
  }

  def parse_sections(
    syntax: Outer_Syntax,
    node_name: Document.Node.Name,
    text: CharSequence): List[Document] =
  {
    /* stack operations */

    def buffer(): mutable.ListBuffer[Document] =
      new mutable.ListBuffer[Document]

    var stack: List[(Int, Command, mutable.ListBuffer[Document])] =
      List((0, Command.empty, buffer()))

    @tailrec def close(level: Int => Boolean)
    {
      stack match {
        case (lev, command, body) :: (_, _, body2) :: rest if level(lev) =>
          body2 += Block(command.span.name, command.source, body.toList)
          stack = stack.tail
          close(level)
        case _ =>
      }
    }

    def result(): List[Document] =
    {
      close(_ => true)
      stack.head._3.toList
    }

    def add(command: Command)
    {
      heading_level(syntax.keywords, command) match {
        case Some(i) =>
          close(_ > i)
          stack = (i + 1, command, buffer()) :: stack
        case None =>
      }
      stack.head._3 += Atom(command)
    }


    /* result structure */

    val spans = syntax.parse_spans(text)
    spans.foreach(span => add(Command(Document_ID.none, node_name, Command.no_blobs, span)))
    result()
  }
}
