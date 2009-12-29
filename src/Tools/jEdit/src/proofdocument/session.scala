/*
 * Isabelle session, potentially with running prover
 *
 * @author Makarius
 */

package isabelle.proofdocument


import scala.actors.Actor._

object Session
{
  case object Global_Settings
}


class Session(system: Isabelle_System)
{
  /* unique ids */

  private var id_count: BigInt = 0
  def create_id(): String = synchronized { id_count += 1; "j" + id_count }


  /* main actor */

  private case class Start(args: List[String])
  private case object Stop

  @volatile private var _syntax = new Outer_Syntax(system.symbols)
  def syntax(): Outer_Syntax = _syntax

  private var prover: Isabelle_Process with Isar_Document = null
  private var prover_ready = false

  private val session_actor = actor {
    val xml_cache = new XML.Cache(131071)
    loop {
      react {
        case Start(args) =>
          if (prover == null) {
            prover = new Isabelle_Process(system, self, args:_*) with Isar_Document
            reply(())
          }

        case Stop =>  // FIXME clarify
          if (prover != null)
            prover.kill
          prover_ready = false
          
        case change: Change if prover_ready =>
          handle_change(change)

        case result: Isabelle_Process.Result =>
          handle_result(result.cache(xml_cache))

        case bad if prover_ready =>
          System.err.println("session_actor: ignoring bad message " + bad)
      }
    }
  }

  def start(args: List[String]) { session_actor !? Start(args) }
  def stop() { session_actor ! Stop }
  def input(change: Change) { session_actor ! change }


  /* pervasive event buses */

  val global_settings = new Event_Bus[Session.Global_Settings.type]
  val raw_results = new Event_Bus[Isabelle_Process.Result]
  val results = new Event_Bus[Command]

  val command_change = new Event_Bus[Command]
  val document_change = new Event_Bus[Proof_Document]


  /* selected state */  // FIXME!? races!?

  private var _selected_state: Command = null
  def selected_state = _selected_state
  def selected_state_=(state: Command) { _selected_state = state; results.event(state) }


  /* document state information */

  @volatile private var states = Map[Isar_Document.State_ID, Command_State]()
  @volatile private var commands = Map[Isar_Document.Command_ID, Command]()
  val document_0 = Proof_Document.empty(create_id())  // FIXME fresh id (!??)
  @volatile private var document_versions = List(document_0)

  def command(id: Isar_Document.Command_ID): Option[Command] = commands.get(id)
  def document(id: Isar_Document.Document_ID): Option[Proof_Document] =
    document_versions.find(_.id == id)


  /* document changes */

  def begin_document(path: String)
  {
    prover.begin_document(document_0.id, path)   // FIXME fresh document!?!
  }

  private def handle_change(change: Change)
  {
    val old = document(change.parent.get.id).get
    val (doc, changes) = old.text_changed(this, change)
    document_versions ::= doc

    val id_changes = changes map {
      case (c1, c2) =>
        (c1.map(_.id).getOrElse(document_0.id),
         c2 match {
            case None => None
            case Some(command) =>
              commands += (command.id -> command)
              prover.define_command(command.id, system.symbols.encode(command.content))
              Some(command.id)
          })
    }
    prover.edit_document(old.id, doc.id, id_changes)

    document_change.event(doc)
  }


  /* prover results */

  private def handle_result(result: Isabelle_Process.Result)
  {
    raw_results.event(result)

    val state =
      Position.id_of(result.props) match {
        case None => None
        case Some(id) => commands.get(id) orElse states.get(id) orElse None
      }
    if (state.isDefined) state.get ! (this, result.message)
    else if (result.kind == Isabelle_Process.Kind.STATUS) {
      //{{{ global status message
      for (elem <- result.body) {
        elem match {
          // document edits
          case XML.Elem(Markup.EDITS, (Markup.ID, doc_id) :: _, edits) =>
            document_versions.find(_.id == doc_id) match {
              case Some(doc) =>
                for {
                  XML.Elem(Markup.EDIT, (Markup.ID, cmd_id) :: (Markup.STATE, state_id) :: _, _)
                  <- edits }
                {
                  commands.get(cmd_id) match {
                    case Some(cmd) =>
                      val state = new Command_State(cmd)
                      states += (state_id -> state)
                      doc.states += (cmd -> state)
                      command_change.event(cmd)   // FIXME really!?
                    case None =>
                  }
                }
              case None =>
            }

          // command and keyword declarations
          case XML.Elem(Markup.COMMAND_DECL, (Markup.NAME, name) :: (Markup.KIND, kind) :: _, _) =>
            _syntax += (name, kind)
          case XML.Elem(Markup.KEYWORD_DECL, (Markup.NAME, name) :: _, _) =>
            _syntax += name

          // process ready (after initialization)
          case XML.Elem(Markup.READY, _, _) => prover_ready = true

        case _ =>
        }
      }
      //}}}
    }
    else if (result.kind == Isabelle_Process.Kind.EXIT)
      prover = null
  }
}
