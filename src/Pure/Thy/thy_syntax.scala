/*  Title:      Pure/Thy/thy_syntax.scala
    Author:     Makarius

Superficial theory syntax: tokens and spans.
*/

package isabelle


import scala.collection.mutable
import scala.annotation.tailrec


object Thy_Syntax
{
  /** parse spans **/

  def parse_spans(toks: List[Token]): List[List[Token]] =
  {
    val result = new mutable.ListBuffer[List[Token]]
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



  /** text edits **/

  def text_edits(session: Session, old_doc: Document, edits: List[Document.Node_Text_Edit])
      : (List[Document.Edit[Command]], Document) =
  {
    /* phase 1: edit individual command source */

    @tailrec def edit_text(eds: List[Text_Edit], commands: Linear_Set[Command])
        : Linear_Set[Command] =
    {
      eds match {
        case e :: es =>
          Document.Node.command_starts(commands.iterator).find {
            case (cmd, cmd_start) =>
              e.can_edit(cmd.source, cmd_start) ||
                e.is_insert && e.start == cmd_start + cmd.length
          } match {
            case Some((cmd, cmd_start)) if e.can_edit(cmd.source, cmd_start) =>
              val (rest, text) = e.edit(cmd.source, cmd_start)
              val new_commands = commands.insert_after(Some(cmd), Command.unparsed(text)) - cmd
              edit_text(rest.toList ::: es, new_commands)

            case Some((cmd, cmd_start)) =>
              edit_text(es, commands.insert_after(Some(cmd), Command.unparsed(e.text)))

            case None =>
              require(e.is_insert && e.start == 0)
              edit_text(es, commands.insert_after(None, Command.unparsed(e.text)))
          }
        case Nil => commands
      }
    }


    /* phase 2: recover command spans */

    @tailrec def recover_spans(commands: Linear_Set[Command]): Linear_Set[Command] =
    {
      commands.iterator.find(_.is_unparsed) match {
        case Some(first_unparsed) =>
          val first =
            commands.reverse_iterator(first_unparsed).find(_.is_command) getOrElse commands.head
          val last =
            commands.iterator(first_unparsed).find(_.is_command) getOrElse commands.last
          val range =
            commands.iterator(first).takeWhile(_ != last).toList ::: List(last)

          val sources = range.flatMap(_.span.map(_.source))
          val spans0 = parse_spans(session.current_syntax.scan(sources.mkString))

          val (before_edit, spans1) =
            if (!spans0.isEmpty && first.is_command && first.span == spans0.head)
              (Some(first), spans0.tail)
            else (commands.prev(first), spans0)

          val (after_edit, spans2) =
            if (!spans1.isEmpty && last.is_command && last.span == spans1.last)
              (Some(last), spans1.take(spans1.length - 1))
            else (commands.next(last), spans1)

          val inserted = spans2.map(span => new Command(session.create_id(), span))
          val new_commands =
            commands.delete_between(before_edit, after_edit).append_after(before_edit, inserted)
          recover_spans(new_commands)

        case None => commands
      }
    }


    /* resulting document edits */

    {
      val doc_edits = new mutable.ListBuffer[Document.Edit[Command]]
      var nodes = old_doc.nodes

      for ((name, text_edits) <- edits) {
        val commands0 = nodes(name).commands
        val commands1 = edit_text(text_edits, commands0)
        val commands2 = recover_spans(commands1)   // FIXME somewhat slow

        val removed_commands = commands0.iterator.filter(!commands2.contains(_)).toList
        val inserted_commands = commands2.iterator.filter(!commands0.contains(_)).toList

        val cmd_edits =
          removed_commands.reverse.map(cmd => (commands0.prev(cmd), None)) :::
          inserted_commands.map(cmd => (commands2.prev(cmd), Some(cmd)))

        doc_edits += (name -> Some(cmd_edits))
        nodes += (name -> new Document.Node(commands2))
      }
      (doc_edits.toList, new Document(session.create_id(), nodes))
    }
  }
}
