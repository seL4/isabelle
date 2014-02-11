/*  Title:      Pure/PIDE/protocol.scala
    Author:     Makarius

Protocol message formats for interactive proof documents.
*/

package isabelle


object Protocol
{
  /* document editing */

  object Assign_Update
  {
    def unapply(text: String): Option[(Document_ID.Version, Document.Assign_Update)] =
      try {
        import XML.Decode._
        val body = YXML.parse_body(text)
        Some(pair(long, list(pair(long, list(long))))(body))
      }
      catch {
        case ERROR(_) => None
        case _: XML.Error => None
      }
  }

  object Removed
  {
    def unapply(text: String): Option[List[Document_ID.Version]] =
      try {
        import XML.Decode._
        Some(list(long)(YXML.parse_body(text)))
      }
      catch {
        case ERROR(_) => None
        case _: XML.Error => None
      }
  }


  /* command status */

  object Status
  {
    val init = Status()
  }

  sealed case class Status(
    private val touched: Boolean = false,
    private val accepted: Boolean = false,
    private val failed: Boolean = false,
    forks: Int = 0,
    runs: Int = 0)
  {
    def + (that: Status): Status =
      Status(touched || that.touched, accepted || that.accepted, failed || that.failed,
        forks + that.forks, runs + that.runs)

    def is_unprocessed: Boolean = accepted && !failed && (!touched || (forks != 0 && runs == 0))
    def is_running: Boolean = runs != 0
    def is_finished: Boolean = !failed && touched && forks == 0 && runs == 0
    def is_failed: Boolean = failed
  }

  val command_status_markup: Set[String] =
    Set(Markup.ACCEPTED, Markup.FORKED, Markup.JOINED, Markup.RUNNING,
      Markup.FINISHED, Markup.FAILED)

  def command_status(status: Status, markup: Markup): Status =
    markup match {
      case Markup(Markup.ACCEPTED, _) => status.copy(accepted = true)
      case Markup(Markup.FORKED, _) => status.copy(touched = true, forks = status.forks + 1)
      case Markup(Markup.JOINED, _) => status.copy(forks = status.forks - 1)
      case Markup(Markup.RUNNING, _) => status.copy(touched = true, runs = status.runs + 1)
      case Markup(Markup.FINISHED, _) => status.copy(runs = status.runs - 1)
      case Markup(Markup.FAILED, _) => status.copy(failed = true)
      case _ => status
    }

  def command_status(markups: List[Markup]): Status =
    (Status.init /: markups)(command_status(_, _))


  /* command timing */

  object Command_Timing
  {
    def unapply(props: Properties.T): Option[(Document_ID.Generic, isabelle.Timing)] =
      props match {
        case (Markup.FUNCTION, Markup.COMMAND_TIMING) :: args =>
          (args, args) match {
            case (Position.Id(id), Markup.Timing_Properties(timing)) => Some((id, timing))
            case _ => None
          }
        case _ => None
      }
  }


  /* node status */

  sealed case class Node_Status(
    unprocessed: Int, running: Int, finished: Int, warned: Int, failed: Int)
  {
    def total: Int = unprocessed + running + finished + warned + failed
  }

  def node_status(
    state: Document.State, version: Document.Version, node: Document.Node): Node_Status =
  {
    var unprocessed = 0
    var running = 0
    var finished = 0
    var warned = 0
    var failed = 0
    node.commands.foreach(command =>
      {
        val st = state.command_state(version, command)
        val status = command_status(st.status)
        if (status.is_running) running += 1
        else if (status.is_finished) {
          if (st.results.entries.exists(p => is_warning(p._2))) warned += 1
          else finished += 1
        }
        else if (status.is_failed) failed += 1
        else unprocessed += 1
      })
    Node_Status(unprocessed, running, finished, warned, failed)
  }


  /* node timing */

  sealed case class Node_Timing(total: Double, commands: Map[Command, Double])

  val empty_node_timing = Node_Timing(0.0, Map.empty)

  def node_timing(
    state: Document.State,
    version: Document.Version,
    node: Document.Node,
    threshold: Double): Node_Timing =
  {
    var total = 0.0
    var commands = Map.empty[Command, Double]
    for {
      command <- node.commands.iterator
      st = state.command_state(version, command)
      command_timing =
        (0.0 /: st.status)({
          case (timing, Markup.Timing(t)) => timing + t.elapsed.seconds
          case (timing, _) => timing
        })
    } {
      total += command_timing
      if (command_timing >= threshold) commands += (command -> command_timing)
    }
    Node_Timing(total, commands)
  }


  /* result messages */

  private val clean = Set(Markup.REPORT, Markup.NO_REPORT)

  def clean_message(body: XML.Body): XML.Body =
    body filter {
      case XML.Wrapped_Elem(Markup(name, _), _, _) => !clean(name)
      case XML.Elem(Markup(name, _), _) => !clean(name)
      case _ => true
    } map {
      case XML.Wrapped_Elem(markup, body, ts) => XML.Wrapped_Elem(markup, body, clean_message(ts))
      case XML.Elem(markup, ts) => XML.Elem(markup, clean_message(ts))
      case t => t
    }

  def message_reports(props: Properties.T, body: XML.Body): List[XML.Elem] =
    body flatMap {
      case XML.Wrapped_Elem(Markup(Markup.REPORT, ps), body, ts) =>
        List(XML.Wrapped_Elem(Markup(Markup.REPORT, props ::: ps), body, ts))
      case XML.Elem(Markup(Markup.REPORT, ps), ts) =>
        List(XML.Elem(Markup(Markup.REPORT, props ::: ps), ts))
      case XML.Wrapped_Elem(_, _, ts) => message_reports(props, ts)
      case XML.Elem(_, ts) => message_reports(props, ts)
      case XML.Text(_) => Nil
    }


  /* specific messages */

  def is_inlined(msg: XML.Tree): Boolean =
    !(is_result(msg) || is_tracing(msg) || is_state(msg))

  def is_result(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Markup.RESULT, _), _) => true
      case _ => false
    }

  def is_tracing(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Markup.TRACING, _), _) => true
      case XML.Elem(Markup(Markup.TRACING_MESSAGE, _), _) => true
      case _ => false
    }

  def is_writeln_markup(msg: XML.Tree, name: String): Boolean =
    msg match {
      case XML.Elem(Markup(Markup.WRITELN, _),
        List(XML.Elem(markup, _))) => markup.name == name
      case XML.Elem(Markup(Markup.WRITELN_MESSAGE, _),
        List(XML.Elem(markup, _))) => markup.name == name
      case _ => false
    }

  def is_state(msg: XML.Tree): Boolean = is_writeln_markup(msg, Markup.STATE)
  def is_information(msg: XML.Tree): Boolean = is_writeln_markup(msg, Markup.INFORMATION)

  def is_warning(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Markup.WARNING, _), _) => true
      case XML.Elem(Markup(Markup.WARNING_MESSAGE, _), _) => true
      case _ => false
    }

  def is_error(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Markup.ERROR, _), _) => true
      case XML.Elem(Markup(Markup.ERROR_MESSAGE, _), _) => true
      case _ => false
    }


  /* dialogs */

  object Dialog_Args
  {
    def unapply(props: Properties.T): Option[(Document_ID.Generic, Long, String)] =
      (props, props, props) match {
        case (Position.Id(id), Markup.Serial(serial), Markup.Result(result)) =>
          Some((id, serial, result))
        case _ => None
      }
  }

  object Dialog
  {
    def unapply(tree: XML.Tree): Option[(Document_ID.Generic, Long, String)] =
      tree match {
        case XML.Elem(Markup(Markup.DIALOG, Dialog_Args(id, serial, result)), _) =>
          Some((id, serial, result))
        case _ => None
      }
  }

  object Dialog_Result
  {
    def apply(id: Document_ID.Generic, serial: Long, result: String): XML.Elem =
    {
      val props = Position.Id(id) ::: Markup.Serial(serial)
      XML.Elem(Markup(Markup.RESULT, props), List(XML.Text(result)))
    }

    def unapply(tree: XML.Tree): Option[String] =
      tree match {
        case XML.Elem(Markup(Markup.RESULT, _), List(XML.Text(result))) => Some(result)
        case _ => None
      }
  }


  /* reported positions */

  private val include_pos = Set(Markup.BINDING, Markup.ENTITY, Markup.REPORT, Markup.POSITION)

  def message_positions(command: Command, message: XML.Elem): Set[Text.Range] =
  {
    def elem_positions(raw_range: Text.Range, set: Set[Text.Range], body: XML.Body)
      : Set[Text.Range] =
    {
      val range = command.decode(raw_range).restrict(command.range)
      body.foldLeft(if (range.is_singularity) set else set + range)(positions)
    }

    def positions(set: Set[Text.Range], tree: XML.Tree): Set[Text.Range] =
      tree match {
        case XML.Wrapped_Elem(Markup(name, Position.Reported(id, file, range)), _, body)
        if include_pos(name) && id == command.id && file == "" => elem_positions(range, set, body)

        case XML.Elem(Markup(name, Position.Reported(id, file, range)), body)
        if include_pos(name) && id == command.id && file == "" => elem_positions(range, set, body)

        case XML.Wrapped_Elem(_, _, body) => body.foldLeft(set)(positions)

        case XML.Elem(_, body) => body.foldLeft(set)(positions)

        case _ => set
      }

    val set = positions(Set.empty, message)
    if (set.isEmpty)
      set ++ Position.Range.unapply(message.markup.properties).map(command.decode(_))
    else set
  }
}


trait Protocol extends Isabelle_Process
{
  /* inlined files */

  def define_blob(blob: Bytes): Unit =
    protocol_command_raw("Document.define_blob", Bytes(blob.sha1_digest.toString), blob)


  /* commands */

  def define_command(command: Command): Unit =
  {
    val blobs_yxml =
    { import XML.Encode._
      val encode_blob: T[Command.Blob] =
        variant(List(
          { case Exn.Res((a, b)) =>
              (Nil, pair(string, option(string))((a.node, b.map(_.toString)))) },
          { case Exn.Exn(e) => (Nil, string(Exn.message(e))) }))
      YXML.string_of_body(list(encode_blob)(command.blobs))
    }
    protocol_command("Document.define_command",
      Document_ID(command.id), encode(command.name), blobs_yxml, encode(command.source))
  }


  /* execution */

  def discontinue_execution(): Unit =
    protocol_command("Document.discontinue_execution")

  def cancel_exec(id: Document_ID.Exec): Unit =
    protocol_command("Document.cancel_exec", Document_ID(id))


  /* document versions */

  def update(old_id: Document_ID.Version, new_id: Document_ID.Version,
    edits: List[Document.Edit_Command])
  {
    val edits_yxml =
    { import XML.Encode._
      def id: T[Command] = (cmd => long(cmd.id))
      def encode_edit(name: Document.Node.Name)
          : T[Document.Node.Edit[Command.Edit, Command.Perspective]] =
        variant(List(
          { case Document.Node.Edits(a) => (Nil, list(pair(option(id), option(id)))(a)) },
          { case Document.Node.Deps(header) =>
              val master_dir = Isabelle_System.posix_path(name.master_dir)
              val imports = header.imports.map(_.node)
              val keywords = header.keywords.map({ case (a, b, _) => (a, b) })
              (Nil,
                pair(Encode.string, pair(Encode.string, pair(list(Encode.string),
                  pair(list(pair(Encode.string,
                    option(pair(pair(Encode.string, list(Encode.string)), list(Encode.string))))),
                  list(Encode.string)))))(
                (master_dir, (name.theory, (imports, (keywords, header.errors)))))) },
          { case Document.Node.Perspective(a, b, c) =>
              (bool_atom(a) :: b.commands.map(cmd => long_atom(cmd.id)),
                list(pair(id, pair(Encode.string, list(Encode.string))))(c.dest)) }))
      def encode_edits: T[List[Document.Edit_Command]] = list((node_edit: Document.Edit_Command) =>
      {
        val (name, edit) = node_edit
        pair(string, encode_edit(name))(name.node, edit)
      })
      YXML.string_of_body(encode_edits(edits)) }
    protocol_command("Document.update", Document_ID(old_id), Document_ID(new_id), edits_yxml)
  }

  def remove_versions(versions: List[Document.Version])
  {
    val versions_yxml =
      { import XML.Encode._
        YXML.string_of_body(list(long)(versions.map(_.id))) }
    protocol_command("Document.remove_versions", versions_yxml)
  }


  /* dialog via document content */

  def dialog_result(serial: Long, result: String): Unit =
    protocol_command("Document.dialog_result", Properties.Value.Long(serial), result)
}
