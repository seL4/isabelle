/*  Title:      Pure/System/session.scala
    Author:     Makarius
    Options:    :folding=explicit:collapseFolds=1:

Isabelle session, potentially with running prover.
*/

package isabelle


import scala.actors.TIMEOUT
import scala.actors.Actor
import scala.actors.Actor._


object Session
{
  /* events */

  case object Global_Settings
  case object Perspective
  case class Commands_Changed(set: Set[Command])



  /* managed entities */

  trait Entity
  {
    val id: Document.ID
    def consume(message: XML.Tree, forward: Command => Unit): Unit
  }
}


class Session(system: Isabelle_System)
{
  /* real time parameters */  // FIXME properties or settings (!?)

  // user input (e.g. text edits, cursor movement)
  val input_delay = 300

  // prover output (markup, common messages)
  val output_delay = 100

  // GUI layout updates
  val update_delay = 500


  /* pervasive event buses */

  val global_settings = new Event_Bus[Session.Global_Settings.type]
  val raw_results = new Event_Bus[Isabelle_Process.Result]
  val raw_output = new Event_Bus[Isabelle_Process.Result]
  val commands_changed = new Event_Bus[Session.Commands_Changed]
  val perspective = new Event_Bus[Session.Perspective.type]


  /* unique ids */

  private var id_count: Document.ID = 0
  def create_id(): Document.ID = synchronized {
    require(id_count > java.lang.Long.MIN_VALUE)
    id_count -= 1
    id_count
  }



  /** main actor **/

  @volatile private var syntax = new Outer_Syntax(system.symbols)
  def current_syntax: Outer_Syntax = syntax

  @volatile private var entities = Map[Document.ID, Session.Entity]()
  def lookup_entity(id: Document.ID): Option[Session.Entity] = entities.get(id)
  def lookup_command(id: Document.ID): Option[Command] =
    lookup_entity(id) match {
      case Some(cmd: Command) => Some(cmd)
      case _ => None
    }

  private case class Started(timeout: Int, args: List[String])
  private case object Stop

  private lazy val session_actor = actor {

    var prover: Isabelle_Process with Isar_Document = null

    def register(entity: Session.Entity) { entities += (entity.id -> entity) }

    var documents = Map[Document.Version_ID, Document]()
    def register_document(doc: Document) { documents += (doc.id -> doc) }
    register_document(Document.init)


    /* document changes */

    def handle_change(change: Document.Change)
    //{{{
    {
      require(change.parent.isDefined)

      val (node_edits, doc) = change.result.join
      val id_edits =
        node_edits map {
          case (name, None) => (name, None)
          case (name, Some(cmd_edits)) =>
            val chs =
              cmd_edits map {
                case (c1, c2) =>
                  val id1 = c1.map(_.id)
                  val id2 =
                    c2 match {
                      case None => None
                      case Some(command) =>
                        if (!lookup_command(command.id).isDefined) {
                          register(command)
                          prover.define_command(command.id, system.symbols.encode(command.source))
                        }
                        Some(command.id)
                    }
                  (id1, id2)
              }
            (name -> Some(chs))
        }
      register_document(doc)
      prover.edit_document(change.parent.get.id, doc.id, id_edits)
    }
    //}}}


    /* prover results */

    def bad_result(result: Isabelle_Process.Result)
    {
      System.err.println("Ignoring prover result: " + result.message.toString)
    }

    def handle_result(result: Isabelle_Process.Result)
    //{{{
    {
      raw_results.event(result)

      val target_id: Option[Document.ID] = Position.get_id(result.properties)
      val target: Option[Session.Entity] =
        target_id match {
          case None => None
          case Some(id) => lookup_entity(id)
        }
      if (target.isDefined) target.get.consume(result.message, indicate_command_change)
      else if (result.is_status) {
        // global status message
        result.body match {

          // execution assignment
          case List(Isar_Document.Assign(edits)) if target_id.isDefined =>
            documents.get(target_id.get) match {
              case Some(doc) =>
                val execs =
                  for {
                    Isar_Document.Edit(cmd_id, exec_id) <- edits
                    cmd <- lookup_command(cmd_id)
                  } yield {
                    val st = cmd.assign_exec(exec_id)  // FIXME session state
                    register(st)
                    (cmd, st)
                  }
                doc.assign_execs(execs)  // FIXME session state
              case None => bad_result(result)
            }

          // keyword declarations
          case List(Keyword.Command_Decl(name, kind)) => syntax += (name, kind)
          case List(Keyword.Keyword_Decl(name)) => syntax += name

          case _ => if (!result.is_ready) bad_result(result)
        }
      }
      else if (result.kind == Markup.EXIT)
        prover = null
      else if (result.is_raw)
        raw_output.event(result)
      else if (!result.is_system)   // FIXME syslog (!?)
        bad_result(result)
    }
    //}}}


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
          if result.kind == Markup.INIT =>
          while (receive {
            case result: Isabelle_Process.Result =>
              handle_result(result); !result.is_ready
            }) {}
          None

        case result: Isabelle_Process.Result
          if result.kind == Markup.EXIT =>
          Some(startup_error())

        case TIMEOUT =>  // FIXME clarify
          prover.kill; Some(startup_error())
      }
    }


    /* main loop */

    val xml_cache = new XML.Cache(131071)

    loop {
      react {
        case Started(timeout, args) =>
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

        case change: Document.Change if prover != null =>
          handle_change(change)

        case result: Isabelle_Process.Result =>
          handle_result(result.cache(xml_cache))

        case TIMEOUT =>  // FIXME clarify!

        case bad if prover != null =>
          System.err.println("session_actor: ignoring bad message " + bad)
      }
    }
  }



  /** buffered command changes (delay_first discipline) **/

  private lazy val command_change_buffer = actor
  //{{{
  {
    import scala.compat.Platform.currentTime

    var changed: Set[Command] = Set()
    var flush_time: Option[Long] = None

    def flush_timeout: Long =
      flush_time match {
        case None => 5000L
        case Some(time) => (time - currentTime) max 0
      }

    def flush()
    {
      if (!changed.isEmpty) commands_changed.event(Session.Commands_Changed(changed))
      changed = Set()
      flush_time = None
    }

    def invoke()
    {
      val now = currentTime
      flush_time match {
        case None => flush_time = Some(now + output_delay)
        case Some(time) => if (now >= time) flush()
      }
    }

    loop {
      reactWithin(flush_timeout) {
        case command: Command => changed += command; invoke()
        case TIMEOUT => flush()
        case bad => System.err.println("command_change_buffer: ignoring bad message " + bad)
      }
    }
  }
  //}}}

  def indicate_command_change(command: Command)
  {
    command_change_buffer ! command
  }



  /** editor history **/

  private case class Edit_Document(edits: List[Document.Node_Text_Edit])

  private val editor_history = new Actor
  {
    @volatile private var history = Document.Change.init
    def current_change(): Document.Change = history

    def act
    {
      loop {
        react {
          case Edit_Document(edits) =>
            val old_change = history
            val new_id = create_id()
            val result: isabelle.Future[(List[Document.Edit[Command]], Document)] =
              isabelle.Future.fork {
                val old_doc = old_change.join_document
                old_doc.await_assignment
                Document.text_edits(Session.this, old_doc, new_id, edits)
              }
            val new_change = new Document.Change(new_id, Some(old_change), edits, result)
            history = new_change
            new_change.result.map(_ => session_actor ! new_change)
            reply(())

          case bad => System.err.println("editor_model: ignoring bad message " + bad)
        }
      }
    }
  }
  editor_history.start



  /** main methods **/

  def started(timeout: Int, args: List[String]): Option[String] =
    (session_actor !? Started(timeout, args)).asInstanceOf[Option[String]]

  def stop() { session_actor ! Stop }

  def snapshot(name: String, pending_edits: List[Text_Edit]): Document.Snapshot =
    editor_history.current_change().snapshot(name, pending_edits)

  def edit_document(edits: List[Document.Node_Text_Edit]) { editor_history !? Edit_Document(edits) }
}
