/*  Title:      Pure/PIDE/isar_document.scala
    Author:     Makarius

Protocol message formats for interactive Isar documents.
*/

package isabelle


object Isar_Document
{
  /* document editing */

  object Assign
  {
    def unapply(text: String): Option[(Document.Version_ID, Document.Assign)] =
      try {
        import XML.Decode._
        val body = YXML.parse_body(text)
        Some(pair(long, pair(list(pair(long, option(long))), list(pair(string, option(long)))))(body))
      }
      catch {
        case ERROR(_) => None
        case _: XML.XML_Atom => None
        case _: XML.XML_Body => None
      }
  }

  object Removed
  {
    def unapply(text: String): Option[List[Document.Version_ID]] =
      try {
        import XML.Decode._
        Some(list(long)(YXML.parse_body(text)))
      }
      catch {
        case ERROR(_) => None
        case _: XML.XML_Atom => None
        case _: XML.XML_Body => None
      }
  }


  /* toplevel transactions */

  sealed abstract class Status
  case object Unprocessed extends Status
  case class Forked(forks: Int) extends Status
  case object Finished extends Status
  case object Failed extends Status

  def command_status(markup: List[Markup]): Status =
  {
    val forks = (0 /: markup) {
      case (i, Markup(Isabelle_Markup.FORKED, _)) => i + 1
      case (i, Markup(Isabelle_Markup.JOINED, _)) => i - 1
      case (i, _) => i
    }
    if (forks != 0) Forked(forks)
    else if (markup.exists(_.name == Isabelle_Markup.FAILED)) Failed
    else if (markup.exists(_.name == Isabelle_Markup.FINISHED)) Finished
    else Unprocessed
  }

  sealed case class Node_Status(unprocessed: Int, running: Int, finished: Int, failed: Int)
  {
    def total: Int = unprocessed + running + finished + failed
  }

  def node_status(
    state: Document.State, version: Document.Version, node: Document.Node): Node_Status =
  {
    var unprocessed = 0
    var running = 0
    var finished = 0
    var failed = 0
    node.commands.foreach(command =>
      command_status(state.command_state(version, command).status) match {
        case Unprocessed => unprocessed += 1
        case Forked(_) => running += 1
        case Finished => finished += 1
        case Failed => failed += 1
      })
    Node_Status(unprocessed, running, finished, failed)
  }


  /* result messages */

  def clean_message(body: XML.Body): XML.Body =
    body filter { case XML.Elem(Markup(Isabelle_Markup.NO_REPORT, _), _) => false case _ => true } map
      { case XML.Elem(markup, ts) => XML.Elem(markup, clean_message(ts)) case t => t }

  def message_reports(msg: XML.Tree): List[XML.Elem] =
    msg match {
      case elem @ XML.Elem(Markup(Isabelle_Markup.REPORT, _), _) => List(elem)
      case XML.Elem(_, body) => body.flatMap(message_reports)
      case XML.Text(_) => Nil
    }


  /* specific messages */

  def is_ready(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Isabelle_Markup.STATUS, _),
        List(XML.Elem(Markup(Isabelle_Markup.READY, _), _))) => true
      case _ => false
    }

 def is_tracing(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Isabelle_Markup.TRACING, _), _) => true
      case _ => false
    }

  def is_warning(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Isabelle_Markup.WARNING, _), _) => true
      case _ => false
    }

  def is_error(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Isabelle_Markup.ERROR, _), _) => true
      case _ => false
    }

  def is_state(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Isabelle_Markup.WRITELN, _),
        List(XML.Elem(Markup(Isabelle_Markup.STATE, _), _))) => true
      case _ => false
    }


  /* reported positions */

  private val include_pos =
    Set(Isabelle_Markup.BINDING, Isabelle_Markup.ENTITY, Isabelle_Markup.REPORT,
      Isabelle_Markup.POSITION)

  def message_positions(command: Command, message: XML.Elem): Set[Text.Range] =
  {
    def positions(set: Set[Text.Range], tree: XML.Tree): Set[Text.Range] =
      tree match {
        case XML.Elem(Markup(name, Position.Id_Range(id, raw_range)), body)
        if include_pos(name) && id == command.id =>
          val range = command.decode(raw_range).restrict(command.range)
          body.foldLeft(if (range.is_singularity) set else set + range)(positions)
        case XML.Elem(Markup(name, _), body) => body.foldLeft(set)(positions)
        case _ => set
      }
    val set = positions(Set.empty, message)
    if (set.isEmpty && !is_state(message))
      set ++ Position.Range.unapply(message.markup.properties).map(command.decode(_))
    else set
  }
}


trait Isar_Document extends Isabelle_Process
{
  /* commands */

  def define_command(command: Command): Unit =
    input("Isar_Document.define_command",
      Document.ID(command.id), Symbol.encode(command.name), Symbol.encode(command.source))


  /* document versions */

  def cancel_execution()
  {
    input("Isar_Document.cancel_execution")
  }

  def update_perspective(old_id: Document.Version_ID, new_id: Document.Version_ID,
    name: Document.Node.Name, perspective: Command.Perspective)
  {
    val ids =
    { import XML.Encode._
      list(long)(perspective.commands.map(_.id)) }

    input("Isar_Document.update_perspective", Document.ID(old_id), Document.ID(new_id),
      name.node, YXML.string_of_body(ids))
  }

  def update(old_id: Document.Version_ID, new_id: Document.Version_ID,
    edits: List[Document.Edit_Command])
  {
    val edits_yxml =
    { import XML.Encode._
      def id: T[Command] = (cmd => long(cmd.id))
      def encode_edit(dir: String)
          : T[Document.Node.Edit[(Option[Command], Option[Command]), Command.Perspective]] =
        variant(List(
          { case Document.Node.Clear() => (Nil, Nil) },
          { case Document.Node.Edits(a) => (Nil, list(pair(option(id), option(id)))(a)) },
          { case Document.Node.Header(Exn.Res(Thy_Header(a, b, c))) =>
              (Nil,
                triple(pair(string, string), list(string), list(pair(string, bool)))(
                  (dir, a), b, c)) },
          { case Document.Node.Header(Exn.Exn(e)) => (List(Exn.message(e)), Nil) },
          { case Document.Node.Perspective(a) => (a.commands.map(c => long_atom(c.id)), Nil) }))
      def encode: T[List[Document.Edit_Command]] = list((node_edit: Document.Edit_Command) =>
      {
        val (name, edit) = node_edit
        val dir = Isabelle_System.posix_path(name.dir)
        pair(string, encode_edit(dir))(name.node, edit)
      })
      YXML.string_of_body(encode(edits)) }
    input("Isar_Document.update", Document.ID(old_id), Document.ID(new_id), edits_yxml)
  }

  def remove_versions(versions: List[Document.Version])
  {
    val versions_yxml =
      { import XML.Encode._
        YXML.string_of_body(list(long)(versions.map(_.id))) }
    input("Isar_Document.remove_versions", versions_yxml)
  }


  /* method invocation service */

  def invoke_scala(id: String, tag: Invoke_Scala.Tag.Value, res: String)
  {
    input("Isar_Document.invoke_scala", id, tag.toString, res)
  }
}
