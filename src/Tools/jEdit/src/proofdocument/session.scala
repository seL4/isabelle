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
  val document_change = new Event_Bus[Document]


  /* unique ids */

  private var id_count: BigInt = 0
  def create_id(): Session.Entity_ID = synchronized { id_count += 1; "j" + id_count }


  /* document state information -- owned by session_actor */

  @volatile private var syntax = new Outer_Syntax(system.symbols)
  def current_syntax: Outer_Syntax = syntax

  @volatile private var entities = Map[Session.Entity_ID, Session.Entity]()
  def lookup_entity(id: Session.Entity_ID): Option[Session.Entity] = entities.get(id)

  // FIXME eliminate
  @volatile private var documents = Map[Isar_Document.Document_ID, Document]()
  def document(id: Isar_Document.Document_ID): Option[Document] = documents.get(id)



  /** main actor **/

  private case class Register(entity: Session.Entity)
  private case class Start(timeout: Int, args: List[String])
  private case object Stop
  private case class Begin_Document(path: String)

  private val session_actor = actor {

    var prover: Isabelle_Process with Isar_Document = null

    def register(entity: Session.Entity) { entities += (entity.id -> entity) }


    /* document changes */

    def handle_change(change: Change)
    {
      require(change.parent.isDefined)

      val (doc, changes) = change.result.join
      val id_changes = changes map {
        case (c1, c2) =>
          (c1.map(_.id).getOrElse(""),
           c2 match {
              case None => None
              case Some(command) =>  // FIXME clarify -- may reuse existing commands!??
                register(command)
                prover.define_command(command.id, system.symbols.encode(command.content))
                Some(command.id)
            })
      }
      register(doc)
      documents += (doc.id -> doc)  // FIXME remove
      prover.edit_document(change.parent.get.document.id, doc.id, id_changes)

      document_change.event(doc)
    }


    /* prover results */

    def handle_result(result: Isabelle_Process.Result)
    {
      raw_results.event(result)

      val target: Option[Session.Entity] =
        Position.get_id(result.props) match {
          case None => None
          case Some(id) => entities.get(id)
        }
      if (target.isDefined) target.get.consume(this, result.message)
      else if (result.kind == Isabelle_Process.Kind.STATUS) {
        // global status message
        for (elem <- result.body) {
          elem match {
            // command and keyword declarations
            case XML.Elem(Markup.COMMAND_DECL, (Markup.NAME, name) :: (Markup.KIND, kind) :: _, _) =>
              syntax += (name, kind)
            case XML.Elem(Markup.KEYWORD_DECL, (Markup.NAME, name) :: _, _) =>
              syntax += name

            case _ =>
          }
        }
      }
      else if (result.kind == Isabelle_Process.Kind.EXIT)
        prover = null
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
        case Register(entity: Session.Entity) =>
          register(entity)
          reply(())

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
          register(doc)
          documents += (id -> doc)
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

  // FIXME private?
  def register_entity(entity: Session.Entity) { session_actor !? Register(entity) }

  def start(timeout: Int, args: List[String]): Option[String] =
    (session_actor !? Start(timeout, args)).asInstanceOf[Option[String]]

  def stop() { session_actor ! Stop }
  def input(change: Change) { session_actor ! change }

  def begin_document(path: String): Document =
    (session_actor !? Begin_Document(path)).asInstanceOf[Document]
}
