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

  @volatile private var global_state = Document.State.init
  private def change_state(f: Document.State => Document.State) { global_state = f(global_state) }
  def current_state(): Document.State = global_state

  private case class Started(timeout: Int, args: List[String])
  private case object Stop

  private lazy val session_actor = actor {

    var prover: Isabelle_Process with Isar_Document = null


    /* document changes */

    def handle_change(change: Document.Change)
    //{{{
    {
      require(change.is_finished)

      val old_doc = change.prev.join
      val (node_edits, doc) = change.result.join

      var former_assignment = current_state().the_assignment(old_doc).join
      for {
        (name, Some(cmd_edits)) <- node_edits
        (prev, None) <- cmd_edits
        removed <- old_doc.nodes(name).commands.get_after(prev)
      } former_assignment -= removed

      val id_edits =
        node_edits map {
          case (name, None) => (name, None)
          case (name, Some(cmd_edits)) =>
            val ids =
              cmd_edits map {
                case (c1, c2) =>
                  val id1 = c1.map(_.id)
                  val id2 =
                    c2 match {
                      case None => None
                      case Some(command) =>
                        if (current_state().lookup_command(command.id).isEmpty) {
                          change_state(_.define_command(command))
                          prover.define_command(command.id, system.symbols.encode(command.source))
                        }
                        Some(command.id)
                    }
                  (id1, id2)
              }
            (name -> Some(ids))
        }
      change_state(_.define_document(doc, former_assignment))
      prover.edit_document(old_doc.id, doc.id, id_edits)
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

      Position.get_id(result.properties) match {
        case Some(state_id) =>
          try {
            val (st, state) = global_state.accumulate(state_id, result.message)
            global_state = state
            indicate_command_change(st.command)
          }
          catch { case _: Document.State.Fail => bad_result(result) }
        case None =>
          if (result.is_status) {
            result.body match {
              case List(Isar_Document.Assign(doc_id, edits)) =>
                try { change_state(_.assign(doc_id, edits)) }
                catch { case _: Document.State.Fail => bad_result(result) }
              case List(Keyword.Command_Decl(name, kind)) => syntax += (name, kind)
              case List(Keyword.Keyword_Decl(name)) => syntax += name
              case _ => if (!result.is_ready) bad_result(result)
            }
          }
          else if (result.kind == Markup.EXIT) prover = null
          else if (result.is_raw) raw_output.event(result)
          else if (!result.is_system) bad_result(result)  // FIXME syslog for system messages (!?)
        }
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
    @volatile private var history = List(Document.Change.init)

    def snapshot(name: String, pending_edits: List[Text_Edit]): Document.Snapshot =
    {
      val state_snapshot = current_state()
      val history_snapshot = history

      val found_stable = history_snapshot.find(change =>
        change.is_finished && state_snapshot.is_assigned(change.document.join))
      require(found_stable.isDefined)
      val stable = found_stable.get
      val latest = history_snapshot.head

      val edits =
        (pending_edits /: history_snapshot.takeWhile(_ != stable))((edits, change) =>
            (for ((a, eds) <- change.edits if a == name) yield eds).flatten ::: edits)
      lazy val reverse_edits = edits.reverse

      new Document.Snapshot {
        val document = stable.document.join
        val node = document.nodes(name)
        val is_outdated = !(pending_edits.isEmpty && latest == stable)
        def convert(offset: Int): Int = (offset /: edits)((i, edit) => edit.convert(i))
        def revert(offset: Int): Int = (offset /: reverse_edits)((i, edit) => edit.revert(i))
        def lookup_command(id: Document.Command_ID): Option[Command] =
          state_snapshot.lookup_command(id)
        def state(command: Command): Command.State =
          state_snapshot.command_state(document, command)
      }
    }

    def act
    {
      loop {
        react {
          case Edit_Document(edits) =>
            val history_snapshot = history
            require(!history_snapshot.isEmpty)

            val prev = history_snapshot.head.document
            val result: isabelle.Future[(List[Document.Edit[Command]], Document)] =
              isabelle.Future.fork {
                val old_doc = prev.join
                val former_assignment = current_state().the_assignment(old_doc).join  // FIXME async!?
                Thy_Syntax.text_edits(Session.this, old_doc, edits)
              }
            val new_change = new Document.Change(prev, edits, result)
            history ::= new_change
            new_change.document.map(_ => session_actor ! new_change)
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
    editor_history.snapshot(name, pending_edits)

  def edit_document(edits: List[Document.Node_Text_Edit]) { editor_history !? Edit_Document(edits) }
}
