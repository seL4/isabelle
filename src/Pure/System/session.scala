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
  case object Assignment
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
  val raw_protocol = new Event_Bus[Isabelle_Process.Result]
  val raw_output = new Event_Bus[Isabelle_Process.Result]
  val commands_changed = new Event_Bus[Session.Commands_Changed]
  val perspective = new Event_Bus[Session.Perspective.type]
  val assignments = new Event_Bus[Session.Assignment.type]


  /* unique ids */

  private var id_count: Document.ID = 0
  def new_id(): Document.ID = synchronized {
    require(id_count > java.lang.Long.MIN_VALUE)
    id_count -= 1
    id_count
  }



  /** buffered command changes (delay_first discipline) **/

  private case object Stop

  private val command_change_buffer = Simple_Thread.actor("command_change_buffer", daemon = true)
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

    var finished = false
    while (!finished) {
      receiveWithin(flush_timeout) {
        case command: Command => changed += command; invoke()
        case TIMEOUT => flush()
        case Stop => finished = true
        case bad => System.err.println("command_change_buffer: ignoring bad message " + bad)
      }
    }
  }
  //}}}



  /** main protocol actor **/

  @volatile private var syntax = new Outer_Syntax(system.symbols)
  def current_syntax(): Outer_Syntax = syntax

  private val global_state = new Volatile(Document.State.init)
  def current_state(): Document.State = global_state.peek()

  private case class Edit_Version(edits: List[Document.Node_Text_Edit])
  private case class Started(timeout: Int, args: List[String])

  private val session_actor = Simple_Thread.actor("session_actor", daemon = true)
  {
    var prover: Isabelle_Process with Isar_Document = null


    /* document changes */

    def handle_change(change: Document.Change)
    //{{{
    {
      val previous = change.previous.get_finished
      val (node_edits, current) = change.result.get_finished

      var former_assignment = global_state.peek().the_assignment(previous).get_finished
      for {
        (name, Some(cmd_edits)) <- node_edits
        (prev, None) <- cmd_edits
        removed <- previous.nodes(name).commands.get_after(prev)
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
                        if (global_state.peek().lookup_command(command.id).isEmpty) {
                          global_state.change(_.define_command(command))
                          prover.define_command(command.id, system.symbols.encode(command.source))
                        }
                        Some(command.id)
                    }
                  (id1, id2)
              }
            (name -> Some(ids))
        }
      global_state.change(_.define_version(current, former_assignment))
      prover.edit_version(previous.id, current.id, id_edits)
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
      raw_protocol.event(result)

      result.properties match {
        case Position.Id(state_id) =>
          try {
            val st = global_state.change_yield(_.accumulate(state_id, result.message))
            command_change_buffer ! st.command
          }
          catch { case _: Document.State.Fail => bad_result(result) }
        case _ =>
          if (result.is_status) {
            result.body match {
              case List(Isar_Document.Assign(id, edits)) =>
                try {
                  val cmds: List[Command] = global_state.change_yield(_.assign(id, edits))
                  for (cmd <- cmds) command_change_buffer ! cmd
                  assignments.event(Session.Assignment)
                }
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

    var finished = false
    while (!finished) {
      receive {
        case Edit_Version(edits) =>
          val previous = global_state.peek().history.tip.current
          val result = Future.fork { Thy_Syntax.text_edits(Session.this, previous.join, edits) }
          val change = global_state.change_yield(_.extend_history(previous, edits, result))

          val this_actor = self
          change.current.map(_ => {
            assignments.await { global_state.peek().is_assigned(previous.get_finished) }
            this_actor ! change })

          reply(())

        case change: Document.Change if prover != null =>
          handle_change(change)

        case result: Isabelle_Process.Result =>
          handle_result(result)

        case Started(timeout, args) =>
          if (prover == null) {
            prover = new Isabelle_Process(system, self, args:_*) with Isar_Document
            val origin = sender
            val opt_err = prover_startup(timeout)
            if (opt_err.isDefined) prover = null
            origin ! opt_err
          }
          else reply(None)

        case Stop => // FIXME synchronous!?
          if (prover != null) {
            prover.kill
            prover = null
            finished = true
          }

        case TIMEOUT =>  // FIXME clarify

        case bad if prover != null =>
          System.err.println("session_actor: ignoring bad message " + bad)
      }
    }
  }



  /** main methods **/

  def started(timeout: Int, args: List[String]): Option[String] =
    (session_actor !? Started(timeout, args)).asInstanceOf[Option[String]]

  def stop() { command_change_buffer ! Stop; session_actor ! Stop }

  def edit_version(edits: List[Document.Node_Text_Edit]) { session_actor !? Edit_Version(edits) }

  def snapshot(name: String, pending_edits: List[Text.Edit]): Document.Snapshot =
    global_state.peek().snapshot(name, pending_edits)
}
