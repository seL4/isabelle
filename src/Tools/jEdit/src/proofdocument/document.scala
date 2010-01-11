/*
 * Document as list of commands, consisting of lists of tokens
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.proofdocument


import scala.actors.Actor._
import scala.collection.mutable

import java.util.regex.Pattern


object Document
{
  /* command start positions */

  def command_starts(commands: Linear_Set[Command]): Iterator[(Command, Int)] =
  {
    var offset = 0
    for (cmd <- commands.elements) yield {
      val start = offset
      offset += cmd.length
      (cmd, start)
    }
  }


  /* empty document */

  def empty(id: Isar_Document.Document_ID): Document =
  {
    val doc = new Document(id, Linear_Set(), Map())
    doc.assign_states(Nil)
    doc
  }


  // FIXME
  var phase0: List[Text_Edit] = null
  var phase1: Linear_Set[Command] = null
  var phase2: Linear_Set[Command] = null
  var phase3: List[Edit] = null
  var raw_source: String = null



  /** document edits **/

  type Edit = (Option[Command], Option[Command])

  def text_edits(session: Session, old_doc: Document, new_id: Isar_Document.Document_ID,
    edits: List[Text_Edit]): (List[Edit], Document) =
  {
    require(old_doc.assignment.is_finished)

    phase0 = edits


    /* unparsed dummy commands */

    def unparsed(source: String) =
      new Command(null, List(Outer_Lex.Token(Outer_Lex.Token_Kind.UNPARSED, source)))

    def is_unparsed(command: Command) = command.id == null

    assert(!old_doc.commands.exists(is_unparsed))


    /* phase 1: edit individual command source */

    var commands = old_doc.commands

    def edit_text(eds: List[Text_Edit]): Unit =
    {
      eds match {
        case e :: es =>
          command_starts(commands).find {   // FIXME relative search!
            case (cmd, cmd_start) => e.can_edit(cmd.length, cmd_start)
          } match {  // FIXME try to append after command
            case Some((cmd, cmd_start)) =>
              val (rest, source) = e.edit(cmd.source, cmd_start)
              // FIXME Linear_Set.edit (?)
              commands = commands.insert_after(Some(cmd), unparsed(source))
              commands -= cmd
              edit_text(rest.toList ::: es)

            case None =>
              require(e.isInstanceOf[Text_Edit.Insert] && e.start == 0)
              commands = commands.insert_after(None, unparsed(e.text))
              edit_text(es)
          }
        case Nil =>
      }
    }
    edit_text(edits)

    phase1 = commands


    /* phase 2: command range edits */

    def edit_commands(): Unit =
    {
      // FIXME relative search!
      commands.elements.find(is_unparsed) match {
        case Some(first_unparsed) =>
          val prefix = commands.prev(first_unparsed)
          val body = commands.elements(first_unparsed).takeWhile(is_unparsed).toList
          val suffix = commands.next(body.last)

          val source =
            (prefix.toList ::: body ::: suffix.toList).flatMap(_.span.map(_.source)).mkString
          assert(source != "")
          raw_source = source
          
          val spans0 = Thy_Syntax.parse_spans(session.current_syntax.scan(source))

          val (before_edit, spans1) =
            if (!spans0.isEmpty && Some(spans0.first) == prefix.map(_.span))
              (prefix, spans0.tail)
            else (if (prefix.isDefined) commands.prev(prefix.get) else None, spans0)

          val (after_edit, spans2) =
            if (!spans1.isEmpty && Some(spans1.last) == suffix.map(_.span))
              (suffix, spans1.take(spans1.length - 1))
            else (if (suffix.isDefined) commands.next(suffix.get) else None, spans1)

          val new_commands = spans2.map(span => new Command(session.create_id(), span))

          commands = commands.delete_between(before_edit, after_edit)
          commands = commands.append_after(before_edit, new_commands)

          edit_commands()

        case None =>
      }
    }
    edit_commands()
    
    phase2 = commands


    /* phase 3: resulting document edits */

    val removed_commands = old_doc.commands.elements.filter(!commands.contains(_)).toList
    val inserted_commands = commands.elements.filter(!old_doc.commands.contains(_)).toList

    // FIXME proper order
    val doc_edits =
      removed_commands.reverse.map(cmd => (commands.prev(cmd), None)) :::
      inserted_commands.map(cmd => (commands.prev(cmd), Some(cmd)))

    val former_states = old_doc.assignment.join -- removed_commands

    phase3 = doc_edits
    (doc_edits, new Document(new_id, commands, former_states))
  }
}


class Document(
    val id: Isar_Document.Document_ID,
    val commands: Linear_Set[Command],
    former_states: Map[Command, Command])
{
  /* command ranges */

  def command_starts: Iterator[(Command, Int)] = Document.command_starts(commands)

  def command_start(cmd: Command): Option[Int] =
    command_starts.find(_._1 == cmd).map(_._2)

  def command_range(i: Int): Iterator[(Command, Int)] =
    command_starts dropWhile { case (cmd, start) => start + cmd.length <= i }

  def command_range(i: Int, j: Int): Iterator[(Command, Int)] =
    command_range(i) takeWhile { case (_, start) => start < j }

  def command_at(i: Int): Option[(Command, Int)] =
  {
    val range = command_range(i)
    if (range.hasNext) Some(range.next) else None
  }


  /* command state assignment */

  val assignment = Future.promise[Map[Command, Command]]
  def await_assignment { assignment.join }

  @volatile private var tmp_states = former_states

  def assign_states(new_states: List[(Command, Command)])
  {
    assignment.fulfill(tmp_states ++ new_states)
    tmp_states = Map()
  }

  def current_state(cmd: Command): State =
  {
    require(assignment.is_finished)
    (assignment.join)(cmd).current_state
  }
}
