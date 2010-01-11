/*
 * Document as editable list of commands
 *
 * @author Makarius
 */

package isabelle.proofdocument


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



  /** document edits **/

  type Edit = (Option[Command], Option[Command])

  def text_edits(session: Session, old_doc: Document, new_id: Isar_Document.Document_ID,
    edits: List[Text_Edit]): (List[Edit], Document) =
  {
    require(old_doc.assignment.is_finished)


    /* unparsed dummy commands */

    def unparsed(source: String) =
      new Command(null, List(Outer_Lex.Token(Outer_Lex.Token_Kind.UNPARSED, source)))

    def is_unparsed(command: Command) = command.id == null

    assert(!old_doc.commands.exists(is_unparsed))   // FIXME remove


    /* phase 1: edit individual command source */

    def edit_text(eds: List[Text_Edit], commands: Linear_Set[Command]): Linear_Set[Command] =
    {
      eds match {
        case e :: es =>
          command_starts(commands).find {   // FIXME relative search!
            case (cmd, cmd_start) => e.can_edit(cmd.length, cmd_start)
          } match {
            // FIXME try to append after command
            case Some((cmd, cmd_start)) =>
              val (rest, source) = e.edit(cmd.source, cmd_start)
              val new_commands = commands.insert_after(Some(cmd), unparsed(source)) - cmd
              edit_text(rest.toList ::: es, new_commands)

            case None =>
              require(e.isInstanceOf[Text_Edit.Insert] && e.start == 0)
              edit_text(es, commands.insert_after(None, unparsed(e.text)))
          }
        case Nil => commands
      }
    }


    /* phase 2: command range edits */

    def edit_commands(commands: Linear_Set[Command]): Linear_Set[Command] =
    {
      // FIXME relative search!
      commands.elements.find(is_unparsed) match {
        case Some(first_unparsed) =>
          val prefix = commands.prev(first_unparsed)
          val body = commands.elements(first_unparsed).takeWhile(is_unparsed).toList
          val suffix = commands.next(body.last)

          val sources = (prefix.toList ::: body ::: suffix.toList).flatMap(_.span.map(_.source))
          val span = Thy_Syntax.parse_spans(session.current_syntax.scan(sources.mkString))

          val (before_edit, spans1) =
            if (!span.isEmpty && Some(span.first) == prefix.map(_.span))
              (prefix, span.tail)
            else (if (prefix.isDefined) commands.prev(prefix.get) else None, span)

          val (after_edit, spans2) =
            if (!spans1.isEmpty && Some(spans1.last) == suffix.map(_.span))
              (suffix, spans1.take(spans1.length - 1))
            else (if (suffix.isDefined) commands.next(suffix.get) else None, spans1)

          val inserted = spans2.map(span => new Command(session.create_id(), span))
          val new_commands =
            commands.delete_between(before_edit, after_edit).append_after(before_edit, inserted)
          edit_commands(new_commands)

        case None => commands
      }
    }


    /* phase 3: resulting document edits */

    val commands0 = old_doc.commands
    val commands1 = edit_text(edits, commands0)
    val commands2 = edit_commands(commands1)

    val removed_commands = commands0.elements.filter(!commands2.contains(_)).toList
    val inserted_commands = commands2.elements.filter(!commands0.contains(_)).toList

    // FIXME tune
    val doc_edits =
      removed_commands.reverse.map(cmd => (commands0.prev(cmd), None)) :::
      inserted_commands.map(cmd => (commands2.prev(cmd), Some(cmd)))

    val former_states = old_doc.assignment.join -- removed_commands

    phase0 = edits
    phase1 = commands1
    phase2 = commands2
    phase3 = doc_edits

    (doc_edits, new Document(new_id, commands2, former_states))
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
