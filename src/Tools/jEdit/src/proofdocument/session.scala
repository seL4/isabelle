/*
 * Isabelle session, potentially with running prover
 *
 * @author Makarius
 */

package isabelle.proofdocument


import scala.actors.Actor._

object Session
{
  /* events */

  case object Global_Settings


  /* managed entities */

  type Entity_ID = String

  trait Entity
  {
    val id: Entity_ID
    def consume(session: Session, message: XML.Tree): Unit
  }
}


class Session(system: Isabelle_System)
{
  /* pervasive event buses */

  val global_settings = new Event_Bus[Session.Global_Settings.type]
  val raw_results = new Event_Bus[Isabelle_Process.Result]
  val results = new Event_Bus[Command]

  val command_change = new Event_Bus[Command]
  val document_change = new Event_Bus[Proof_Document]


  /* unique ids */

  private var id_count: BigInt = 0
  def create_id(): Session.Entity_ID = synchronized { id_count += 1; "j" + id_count }


  /* document state information -- owned by session_actor */

  @volatile private var outer_syntax = new Outer_Syntax(system.symbols)
  def syntax(): Outer_Syntax = outer_syntax

  @volatile private var states = Map[Isar_Document.State_ID, Command_State]()
  @volatile private var commands = Map[Isar_Document.Command_ID, Command]()
  @volatile private var documents = Map[Isar_Document.Document_ID, Proof_Document]()

  def state(id: Isar_Document.State_ID): Option[Command_State] = states.get(id)
  def command(id: Isar_Document.Command_ID): Option[Command] = commands.get(id)
  def document(id: Isar_Document.Document_ID): Option[Proof_Document] = documents.get(id)


  /** main actor **/

  private case class Start(args: List[String])
  private case object Stop
  private case class Begin_Document(path: String)

  private val session_actor = actor {

    var prover: Isabelle_Process with Isar_Document = null
    var prover_ready = false


    /* document changes */

    def handle_change(change: Change)
    {
      val old = document(change.parent.get.id).get
      val (doc, changes) = old.text_changed(this, change)

      val id_changes = changes map {
        case (c1, c2) =>
          (c1.map(_.id).getOrElse(""),
           c2 match {
              case None => None
              case Some(command) =>  // FIXME clarify -- may reuse existing commands!??
                commands += (command.id -> command)
                prover.define_command(command.id, system.symbols.encode(command.content))
                Some(command.id)
            })
      }
      documents += (doc.id -> doc)
      prover.edit_document(old.id, doc.id, id_changes)

      document_change.event(doc)
    }


    /* prover results */

    def handle_result(result: Isabelle_Process.Result)
    {
      raw_results.event(result)

      val target: Option[Session.Entity] =
        Position.id_of(result.props) match {
          case None => None
          case Some(id) => commands.get(id) orElse states.get(id) orElse None
        }
      if (target.isDefined) target.get.consume(this, result.message)
      else if (result.kind == Isabelle_Process.Kind.STATUS) {
        //{{{ global status message
        for (elem <- result.body) {
          elem match {
            // document edits
            case XML.Elem(Markup.EDITS, (Markup.ID, doc_id) :: _, edits) =>
              document(doc_id) match {
                case None =>  // FIXME clarify
                case Some(doc) =>
                  for {
                    XML.Elem(Markup.EDIT, (Markup.ID, cmd_id) :: (Markup.STATE, state_id) :: _, _)
                    <- edits }
                  {
                    commands.get(cmd_id) match {
                      case Some(cmd) =>
                        val state = new Command_State(state_id, cmd)
                        states += (state_id -> state)
                        doc.states += (cmd -> state)
                        command_change.event(cmd)   // FIXME really!?
                      case None =>
                    }
                  }
              }

            // command and keyword declarations
            case XML.Elem(Markup.COMMAND_DECL, (Markup.NAME, name) :: (Markup.KIND, kind) :: _, _) =>
              outer_syntax += (name, kind)
            case XML.Elem(Markup.KEYWORD_DECL, (Markup.NAME, name) :: _, _) =>
              outer_syntax += name

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

    val xml_cache = new XML.Cache(131071)


    /* main loop */

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

        case Begin_Document(path: String) if prover_ready =>
          val id = create_id()
          val doc = Proof_Document.empty(id)
          documents += (id -> doc)
          prover.begin_document(id, path)
          reply(doc)

        case change: Change if prover_ready =>
          handle_change(change)

        case result: Isabelle_Process.Result =>
          handle_result(result.cache(xml_cache))

        case bad if prover_ready =>
          System.err.println("session_actor: ignoring bad message " + bad)
      }
    }
  }


  /* main methods */

  def start(args: List[String]) { session_actor !? Start(args) }
  def stop() { session_actor ! Stop }
  def input(change: Change) { session_actor ! change }

  def begin_document(path: String): Proof_Document =
    (session_actor !? Begin_Document(path)).asInstanceOf[Proof_Document]
}
