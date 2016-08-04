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


  private def is_theory_command(keywords: Keyword.Keywords, name: String): Boolean =
    keywords.kinds.get(name) match {
      case Some(kind) => Keyword.theory(kind) && !Keyword.theory_end(kind)
      case None => false
    }

  private def heading_level(keywords: Keyword.Keywords, command: Command): Option[Int] =
  {
    val name = command.span.name
    name match {
      case Thy_Header.CHAPTER => Some(0)
      case Thy_Header.SECTION => Some(1)
      case Thy_Header.SUBSECTION => Some(2)
      case Thy_Header.SUBSUBSECTION => Some(3)
      case Thy_Header.PARAGRAPH => Some(4)
      case Thy_Header.SUBPARAGRAPH => Some(5)
      case _ if is_theory_command(keywords, name) => Some(6)
      case _ => None
    }
  }


  /* context blocks */

  def parse_blocks(
    syntax: Outer_Syntax,
    node_name: Document.Node.Name,
    text: CharSequence): List[Document] =
  {
    def is_plain_theory(command: Command): Boolean =
      is_theory_command(syntax.keywords, command.span.name) &&
      !command.span.is_begin && !command.span.is_end


    /* stack operations */

    def buffer(): mutable.ListBuffer[Document] = new mutable.ListBuffer[Document]

    var stack: List[(Command, mutable.ListBuffer[Document])] =
      List((Command.empty, buffer()))

    def open(command: Command) { stack = (command, buffer()) :: stack }

    def close(): Boolean =
      stack match {
        case (command, body) :: (_, body2) :: _ =>
          body2 += Block(command.span.name, command.source, body.toList)
          stack = stack.tail
          true
        case _ =>
          false
      }

    def flush() { if (is_plain_theory(stack.head._1)) close() }

    def result(): List[Document] =
    {
      while (close()) { }
      stack.head._2.toList
    }

    def add(command: Command)
    {
      if (command.span.is_begin || is_plain_theory(command)) { flush(); open(command) }
      else if (command.span.is_end) { flush(); close() }

      stack.head._2 += Atom(command)
    }


    /* result structure */

    val spans = syntax.parse_spans(text)
    spans.foreach(span => add(Command(Document_ID.none, node_name, Command.no_blobs, span)))
    result()
  }


  /* section headings etc. */

  def parse_sections(
    syntax: Outer_Syntax,
    node_name: Document.Node.Name,
    text: CharSequence): List[Document] =
  {
    /* stack operations */

    def buffer(): mutable.ListBuffer[Document] = new mutable.ListBuffer[Document]

    var stack: List[(Int, Command, mutable.ListBuffer[Document])] =
      List((0, Command.empty, buffer()))

    @tailrec def close(level: Int => Boolean)
    {
      stack match {
        case (lev, command, body) :: (_, _, body2) :: _ if level(lev) =>
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
