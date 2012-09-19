/*  Title:      Pure/System/session.scala
    Author:     Makarius
    Options:    :folding=explicit:collapseFolds=1:

Main Isabelle/Scala session, potentially with running prover process.
*/

package isabelle


import java.lang.System
import java.util.{Timer, TimerTask}

import scala.collection.mutable
import scala.collection.immutable.Queue
import scala.actors.TIMEOUT
import scala.actors.Actor._


object Session
{
  /* events */

  //{{{
  case object Global_Settings
  case object Caret_Focus
  case class Raw_Edits(edits: List[Document.Edit_Text])
  case class Commands_Changed(
    assignment: Boolean, nodes: Set[Document.Node.Name], commands: Set[Command])

  sealed abstract class Phase
  case object Inactive extends Phase
  case object Startup extends Phase  // transient
  case object Failed extends Phase
  case object Ready extends Phase
  case object Shutdown extends Phase  // transient
  //}}}
}


class Session(val thy_load: Thy_Load)
{
  /* global flags */

  @volatile var timing: Boolean = false
  @volatile var verbose: Boolean = false


  /* tuning parameters */

  def output_delay: Time = Time.seconds(0.1)  // prover output (markup, common messages)
  def message_delay: Time = Time.seconds(0.01)  // incoming prover messages
  def prune_delay: Time = Time.seconds(60.0)  // prune history -- delete old versions
  def prune_size: Int = 0  // size of retained history
  def syslog_limit: Int = 100


  /* pervasive event buses */

  val global_settings = new Event_Bus[Session.Global_Settings.type]
  val caret_focus = new Event_Bus[Session.Caret_Focus.type]
  val raw_edits = new Event_Bus[Session.Raw_Edits]
  val commands_changed = new Event_Bus[Session.Commands_Changed]
  val phase_changed = new Event_Bus[Session.Phase]
  val syslog_messages = new Event_Bus[Isabelle_Process.Output]
  val raw_output_messages = new Event_Bus[Isabelle_Process.Output]
  val all_messages = new Event_Bus[Isabelle_Process.Message]  // potential bottle-neck



  /** buffered command changes (delay_first discipline) **/

  //{{{
  private case object Stop

  private val (_, commands_changed_buffer) =
    Simple_Thread.actor("commands_changed_buffer", daemon = true)
  {
    var finished = false
    while (!finished) {
      receive {
        case Stop => finished = true; reply(())
        case changed: Session.Commands_Changed => commands_changed.event(changed)
        case bad => System.err.println("commands_changed_buffer: ignoring bad message " + bad)
      }
    }
  }
  //}}}


  /** pipelined change parsing **/

  //{{{
  private case class Text_Edits(
    previous: Future[Document.Version],
    text_edits: List[Document.Edit_Text],
    version_result: Promise[Document.Version])

  private val (_, change_parser) = Simple_Thread.actor("change_parser", daemon = true)
  {
    var finished = false
    while (!finished) {
      receive {
        case Stop => finished = true; reply(())

        case Text_Edits(previous, text_edits, version_result) =>
          val prev = previous.get_finished
          val (doc_edits, version) =
            Timing.timeit("Thy_Syntax.text_edits", timing) {
              Thy_Syntax.text_edits(thy_load.base_syntax, prev, text_edits)
            }
          version_result.fulfill(version)
          sender ! Change(doc_edits, prev, version)

        case bad => System.err.println("change_parser: ignoring bad message " + bad)
      }
    }
  }
  //}}}



  /** main protocol actor **/

  /* global state */

  private val syslog = Volatile(Queue.empty[XML.Elem])
  def current_syslog(): String = cat_lines(syslog().iterator.map(XML.content))

  @volatile private var _phase: Session.Phase = Session.Inactive
  private def phase_=(new_phase: Session.Phase)
  {
    _phase = new_phase
    phase_changed.event(new_phase)
  }
  def phase = _phase
  def is_ready: Boolean = phase == Session.Ready

  private val global_state = Volatile(Document.State.init)
  def current_state(): Document.State = global_state()

  def recent_syntax(): Outer_Syntax =
  {
    val version = current_state().recent_finished.version.get_finished
    if (version.is_init) thy_load.base_syntax
    else version.syntax
  }

  def snapshot(name: Document.Node.Name = Document.Node.Name.empty,
      pending_edits: List[Text.Edit] = Nil): Document.Snapshot =
    global_state().snapshot(name, pending_edits)


  /* theory files */

  def header_edit(name: Document.Node.Name, header: Document.Node.Header): Document.Edit_Text =
  {
    val header1 =
      if (thy_load.loaded_theories(name.theory))
        header.error("Attempt to update loaded theory " + quote(name.theory))
      else header
    (name, Document.Node.Deps(header1))
  }


  /* actor messages */

  private case class Start(args: List[String])
  private case object Cancel_Execution
  private case class Change(
    doc_edits: List[Document.Edit_Command],
    previous: Document.Version,
    version: Document.Version)
  private case class Messages(msgs: List[Isabelle_Process.Message])

  private val (_, session_actor) = Simple_Thread.actor("session_actor", daemon = true)
  {
    val this_actor = self

    var prune_next = System.currentTimeMillis() + prune_delay.ms


    /* buffered prover messages */

    object receiver
    {
      private var buffer = new mutable.ListBuffer[Isabelle_Process.Message]

      def flush(): Unit = synchronized {
        if (!buffer.isEmpty) {
          val msgs = buffer.toList
          this_actor ! Messages(msgs)
          buffer = new mutable.ListBuffer[Isabelle_Process.Message]
        }
      }
      def invoke(msg: Isabelle_Process.Message): Unit = synchronized {
        buffer += msg
        msg match {
          case output: Isabelle_Process.Output =>
            if (output.is_syslog)
              syslog >> (queue =>
                {
                  val queue1 = queue.enqueue(output.message)
                  if (queue1.length > syslog_limit) queue1.dequeue._2 else queue1
                })
            if (output.is_protocol) flush()
          case _ =>
        }
      }

      private val timer = new Timer("session_actor.receiver", true)
      timer.schedule(new TimerTask { def run = flush }, message_delay.ms, message_delay.ms)

      def cancel() { timer.cancel() }
    }

    var prover: Option[Isabelle_Process with Protocol] = None


    /* delayed command changes */

    object delay_commands_changed
    {
      private var changed_assignment: Boolean = false
      private var changed_nodes: Set[Document.Node.Name] = Set.empty
      private var changed_commands: Set[Command] = Set.empty

      private var flush_time: Option[Long] = None

      def flush_timeout: Long =
        flush_time match {
          case None => 5000L
          case Some(time) => (time - System.currentTimeMillis()) max 0
        }

      def flush()
      {
        if (changed_assignment || !changed_nodes.isEmpty || !changed_commands.isEmpty)
          commands_changed_buffer !
            Session.Commands_Changed(changed_assignment, changed_nodes, changed_commands)
        changed_assignment = false
        changed_nodes = Set.empty
        changed_commands = Set.empty
        flush_time = None
      }

      def invoke(assign: Boolean, commands: List[Command])
      {
        changed_assignment |= assign
        for (command <- commands) {
          changed_nodes += command.node_name
          changed_commands += command
        }
        val now = System.currentTimeMillis()
        flush_time match {
          case None => flush_time = Some(now + output_delay.ms)
          case Some(time) => if (now >= time) flush()
        }
      }
    }


    /* resulting changes */

    def handle_change(change: Change)
    //{{{
    {
      val previous = change.previous
      val version = change.version
      val doc_edits = change.doc_edits

      def id_command(command: Command)
      {
        if (!global_state().defined_command(command.id)) {
          global_state >> (_.define_command(command))
          prover.get.define_command(command)
        }
      }
      doc_edits foreach {
        case (_, edit) =>
          edit foreach { case (c1, c2) => c1 foreach id_command; c2 foreach id_command }
      }

      val assignment = global_state().the_assignment(previous).check_finished
      global_state >> (_.define_version(version, assignment))
      prover.get.update(previous.id, version.id, doc_edits)
    }
    //}}}


    /* prover output */

    def handle_output(output: Isabelle_Process.Output)
    //{{{
    {
      def bad_output(output: Isabelle_Process.Output)
      {
        if (verbose)
          System.err.println("Ignoring prover output: " + output.message.toString)
      }

      output.properties match {

        case Position.Id(state_id) if !output.is_protocol =>
          try {
            val st = global_state >>> (_.accumulate(state_id, output.message))
            delay_commands_changed.invoke(false, List(st.command))
          }
          catch {
            case _: Document.State.Fail => bad_output(output)
          }

        case Isabelle_Markup.Assign_Execs if output.is_protocol =>
          XML.content(output.body) match {
            case Protocol.Assign(id, assign) =>
              try {
                val cmds = global_state >>> (_.assign(id, assign))
                delay_commands_changed.invoke(true, cmds)
              }
              catch { case _: Document.State.Fail => bad_output(output) }
            case _ => bad_output(output)
          }
          // FIXME separate timeout event/message!?
          if (prover.isDefined && System.currentTimeMillis() > prune_next) {
            val old_versions = global_state >>> (_.prune_history(prune_size))
            if (!old_versions.isEmpty) prover.get.remove_versions(old_versions)
            prune_next = System.currentTimeMillis() + prune_delay.ms
          }

        case Isabelle_Markup.Removed_Versions if output.is_protocol =>
          XML.content(output.body) match {
            case Protocol.Removed(removed) =>
              try {
                global_state >> (_.removed_versions(removed))
              }
              catch { case _: Document.State.Fail => bad_output(output) }
            case _ => bad_output(output)
          }

        case Isabelle_Markup.Invoke_Scala(name, id) if output.is_protocol =>
          Future.fork {
            val arg = XML.content(output.body)
            val (tag, res) = Invoke_Scala.method(name, arg)
            prover.get.invoke_scala(id, tag, res)
          }

        case Isabelle_Markup.Cancel_Scala(id) if output.is_protocol =>
          System.err.println("cancel_scala " + id)  // FIXME actually cancel JVM task

        case _ if output.is_init =>
            phase = Session.Ready

        case Isabelle_Markup.Return_Code(rc) if output.is_exit =>
          if (rc == 0) phase = Session.Inactive
          else phase = Session.Failed

        case _ => bad_output(output)
      }
    }
    //}}}


    /* main loop */

    //{{{
    var finished = false
    while (!finished) {
      receiveWithin(delay_commands_changed.flush_timeout) {
        case TIMEOUT => delay_commands_changed.flush()

        case Start(args) if prover.isEmpty =>
          if (phase == Session.Inactive || phase == Session.Failed) {
            phase = Session.Startup
            prover = Some(new Isabelle_Process(receiver.invoke _, args) with Protocol)
          }

        case Stop =>
          if (phase == Session.Ready) {
            global_state >> (_ => Document.State.init)  // FIXME event bus!?
            phase = Session.Shutdown
            prover.get.terminate
            prover = None
            phase = Session.Inactive
          }
          finished = true
          receiver.cancel()
          reply(())

        case Cancel_Execution if prover.isDefined =>
          prover.get.cancel_execution()

        case raw @ Session.Raw_Edits(edits) if prover.isDefined =>
          prover.get.discontinue_execution()

          val previous = global_state().history.tip.version
          val version = Future.promise[Document.Version]
          val change = global_state >>> (_.continue_history(previous, edits, version))
          raw_edits.event(raw)
          change_parser ! Text_Edits(previous, edits, version)

          reply(())

        case Messages(msgs) =>
          msgs foreach {
            case input: Isabelle_Process.Input =>
              all_messages.event(input)

            case output: Isabelle_Process.Output =>
              if (output.is_stdout || output.is_stderr) raw_output_messages.event(output)
              else handle_output(output)
              if (output.is_syslog) syslog_messages.event(output)
              all_messages.event(output)
          }

        case change: Change
        if prover.isDefined && global_state().is_assigned(change.previous) =>
          handle_change(change)

        case bad if !bad.isInstanceOf[Change] =>
          System.err.println("session_actor: ignoring bad message " + bad)
      }
    }
    //}}}
  }


  /* actions */

  def start(args: List[String])
  { session_actor ! Start(args) }

  def stop() { commands_changed_buffer !? Stop; change_parser !? Stop; session_actor !? Stop }

  def cancel_execution() { session_actor ! Cancel_Execution }

  def edit(edits: List[Document.Edit_Text])
  { session_actor !? Session.Raw_Edits(edits) }

  def init_node(name: Document.Node.Name,
    header: Document.Node.Header, perspective: Text.Perspective, text: String)
  {
    edit(List(header_edit(name, header),
      name -> Document.Node.Clear(),
      name -> Document.Node.Edits(List(Text.Edit.insert(0, text))),
      name -> Document.Node.Perspective(perspective)))
  }

  def edit_node(name: Document.Node.Name,
    header: Document.Node.Header, perspective: Text.Perspective, text_edits: List[Text.Edit])
  {
    edit(List(header_edit(name, header),
      name -> Document.Node.Edits(text_edits),
      name -> Document.Node.Perspective(perspective)))
  }
}
