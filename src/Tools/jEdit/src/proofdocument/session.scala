/*
 * Isabelle session, potentially with running prover
 *
 * @author Makarius
 */

package isabelle.proofdocument


import scala.actors.TIMEOUT
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


  /* unique ids */

  private var id_count: BigInt = 0
  def create_id(): Session.Entity_ID = synchronized { id_count += 1; "j" + id_count }



  /** main actor **/

  @volatile private var syntax = new Outer_Syntax(system.symbols)
  def current_syntax: Outer_Syntax = syntax

  @volatile private var entities = Map[Session.Entity_ID, Session.Entity]()
  def lookup_entity(id: Session.Entity_ID): Option[Session.Entity] = entities.get(id)
  def lookup_command(id: Session.Entity_ID): Option[Command] =
    lookup_entity(id) match {
      case Some(cmd: Command) => Some(cmd)
      case _ => None
    }

  private case class Start(timeout: Int, args: List[String])
  private case object Stop
  private case class Begin_Document(path: String)

  private val session_actor = actor {

    var prover: Isabelle_Process with Isar_Document = null

    def register(entity: Session.Entity) { entities += (entity.id -> entity) }

    var documents = Map[Isar_Document.Document_ID, Document]()
    def register_document(doc: Document) { documents += (doc.id -> doc) }


    /* document changes */

    def handle_change(change: Change)
    {
      require(change.parent.isDefined)

      val (changes, doc) = change.result.join
      val id_changes = changes map {
        case (c1, c2) =>
          (c1.map(_.id).getOrElse(""),
           c2 match {
              case None => None
              case Some(command) =>
                if (!lookup_command(command.id).isDefined) {
                  register(command)
                  prover.define_command(command.id, system.symbols.encode(command.content))
                }
                Some(command.id)
            })
      }
      register_document(doc)
      prover.edit_document(change.parent.get.id, doc.id, id_changes)
    }


    /* prover results */

    def bad_result(result: Isabelle_Process.Result)
    {
      System.err.println("Ignoring prover result: " + result)
    }

    def handle_result(result: Isabelle_Process.Result)
    {
      raw_results.event(result)

      val target_id: Option[Session.Entity_ID] = Position.get_id(result.props)
      val target: Option[Session.Entity] =
        target_id match {
          case None => None
          case Some(id) => lookup_entity(id)
        }
      if (target.isDefined) target.get.consume(this, result.message)
      else if (result.kind == Isabelle_Process.Kind.STATUS) {
        // global status message
        result.body match {

          // document state assigment
          case List(XML.Elem(Markup.ASSIGN, _, edits)) if target_id.isDefined =>
            documents.get(target_id.get) match {
              case Some(doc) =>
                val states =
                  for {
                    XML.Elem(Markup.EDIT, (Markup.ID, cmd_id) :: (Markup.STATE, state_id) :: _, _)
                      <- edits
                    cmd <- lookup_command(cmd_id)
                  } yield {
                    val st = cmd.assign_state(state_id)
                    register(st)
                    (cmd, st)
                  }
                doc.assign_states(states)
              case None => bad_result(result)
            }

          // command and keyword declarations
          case List(XML.Elem(Markup.COMMAND_DECL, (Markup.NAME, name) :: (Markup.KIND, kind) :: _, _)) =>
            syntax += (name, kind)
          case List(XML.Elem(Markup.KEYWORD_DECL, (Markup.NAME, name) :: _, _)) =>
            syntax += name

          case _ => if (!result.is_ready) bad_result(result)
        }
      }
      else if (result.kind == Isabelle_Process.Kind.EXIT)
        prover = null
      else if (result.kind != Isabelle_Process.Kind.STDIN && !result.is_raw)
        bad_result(result)
    }


    /* prover startup */

    def startup_error(): String =
    {
      val buf = new StringBuilder
      while (
        receiveWithin(0) {
          case result: Isabelle_Process.Result =>
            if (result.is_raw) {
              for (text <- XML.content(result.message))
                buf.append(text)
            }
            true
          case TIMEOUT => false
        }) {}
      buf.toString
    }

    def prover_startup(timeout: Int): Option[String] =
    {
      receiveWithin(timeout) {
        case result: Isabelle_Process.Result
          if result.kind == Isabelle_Process.Kind.INIT =>
          while (receive {
            case result: Isabelle_Process.Result =>
              handle_result(result); !result.is_ready
            }) {}
          None

        case result: Isabelle_Process.Result
          if result.kind == Isabelle_Process.Kind.EXIT =>
          Some(startup_error())

        case TIMEOUT =>  // FIXME clarify
          prover.kill; Some(startup_error())
      }
    }


    /* main loop */

    val xml_cache = new XML.Cache(131071)

    loop {
      react {
        case Start(timeout, args) =>
          if (prover == null) {
            prover = new Isabelle_Process(system, self, args:_*) with Isar_Document
            val origin = sender
            val opt_err = prover_startup(timeout)
            if (opt_err.isDefined) prover = null
            origin ! opt_err
          }
          else reply(None)

        case Stop =>  // FIXME clarify; synchronous
          if (prover != null) {
            prover.kill
            prover = null
          }

        case Begin_Document(path: String) if prover != null =>
          val id = create_id()
          val doc = Document.empty(id)
          register_document(doc)
          prover.begin_document(id, path)
          reply(doc)

        case change: Change if prover != null =>
          handle_change(change)

        case result: Isabelle_Process.Result =>
          handle_result(result.cache(xml_cache))

        case bad if prover != null =>
          System.err.println("session_actor: ignoring bad message " + bad)
      }
    }
  }


  /* main methods */

  def start(timeout: Int, args: List[String]): Option[String] =
    (session_actor !? Start(timeout, args)).asInstanceOf[Option[String]]

  def stop() { session_actor ! Stop }
  def input(change: Change) { session_actor ! change }

  def begin_document(path: String): Document =
    (session_actor !? Begin_Document(path)).asInstanceOf[Document]
}
