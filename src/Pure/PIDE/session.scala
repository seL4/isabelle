/*  Title:      Pure/PIDE/session.scala
    Author:     Makarius
    Options:    :folding=explicit:collapseFolds=1:

PIDE editor session, potentially with running prover process.
*/

package isabelle


import java.util.{Timer, TimerTask}

import scala.collection.mutable
import scala.collection.immutable.Queue
import scala.actors.TIMEOUT
import scala.actors.Actor._


object Session
{
  /* events */

  //{{{
  case class Statistics(props: Properties.T)
  case class Global_Options(options: Options)
  case object Caret_Focus
  case class Raw_Edits(doc_blobs: Document.Blobs, edits: List[Document.Edit_Text])
  case class Dialog_Result(id: Document_ID.Generic, serial: Long, result: String)
  case class Commands_Changed(
    assignment: Boolean, nodes: Set[Document.Node.Name], commands: Set[Command])

  sealed abstract class Phase
  case object Inactive extends Phase
  case object Startup extends Phase  // transient
  case object Failed extends Phase
  case object Ready extends Phase
  case object Shutdown extends Phase  // transient
  //}}}


  /* protocol handlers */

  type Prover = Isabelle_Process with Protocol

  abstract class Protocol_Handler
  {
    def stop(prover: Prover): Unit = {}
    val functions: Map[String, (Prover, Isabelle_Process.Protocol_Output) => Boolean]
  }

  class Protocol_Handlers(
    handlers: Map[String, Session.Protocol_Handler] = Map.empty,
    functions: Map[String, Isabelle_Process.Protocol_Output => Boolean] = Map.empty)
  {
    def get(name: String): Option[Protocol_Handler] = handlers.get(name)

    def add(prover: Prover, name: String): Protocol_Handlers =
    {
      val (handlers1, functions1) =
        handlers.get(name) match {
          case Some(old_handler) =>
            System.err.println("Redefining protocol handler: " + name)
            old_handler.stop(prover)
            (handlers - name, functions -- old_handler.functions.keys)
          case None => (handlers, functions)
        }

      val (handlers2, functions2) =
        try {
          val new_handler = Class.forName(name).newInstance.asInstanceOf[Protocol_Handler]
          val new_functions =
            for ((a, f) <- new_handler.functions.toList) yield
              (a, (msg: Isabelle_Process.Protocol_Output) => f(prover, msg))

          val dups = for ((a, _) <- new_functions if functions1.isDefinedAt(a)) yield a
          if (!dups.isEmpty) error("Duplicate protocol functions: " + commas_quote(dups))

          (handlers1 + (name -> new_handler), functions1 ++ new_functions)
        }
        catch {
          case exn: Throwable =>
            System.err.println("Failed to initialize protocol handler: " +
              name + "\n" + Exn.message(exn))
            (handlers1, functions1)
        }

      new Protocol_Handlers(handlers2, functions2)
    }

    def invoke(msg: Isabelle_Process.Protocol_Output): Boolean =
      msg.properties match {
        case Markup.Function(a) if functions.isDefinedAt(a) =>
          try { functions(a)(msg) }
          catch {
            case exn: Throwable =>
              System.err.println("Failed invocation of protocol function: " +
                quote(a) + "\n" + Exn.message(exn))
            false
          }
        case _ => false
      }

    def stop(prover: Prover): Protocol_Handlers =
    {
      for ((_, handler) <- handlers) handler.stop(prover)
      new Protocol_Handlers()
    }
  }
}


class Session(val resources: Resources)
{
  /* global flags */

  @volatile var timing: Boolean = false
  @volatile var verbose: Boolean = false


  /* tuning parameters */

  def output_delay: Time = Time.seconds(0.1)  // prover output (markup, common messages)
  def message_delay: Time = Time.seconds(0.1)  // prover input/output messages
  def prune_delay: Time = Time.seconds(60.0)  // prune history -- delete old versions
  def prune_size: Int = 0  // size of retained history
  def syslog_limit: Int = 100
  def reparse_limit: Int = 0


  /* pervasive event buses */

  val statistics = new Event_Bus[Session.Statistics]
  val global_options = new Event_Bus[Session.Global_Options]
  val caret_focus = new Event_Bus[Session.Caret_Focus.type]
  val raw_edits = new Event_Bus[Session.Raw_Edits]
  val commands_changed = new Event_Bus[Session.Commands_Changed]
  val phase_changed = new Event_Bus[Session.Phase]
  val syslog_messages = new Event_Bus[Isabelle_Process.Output]
  val raw_output_messages = new Event_Bus[Isabelle_Process.Output]
  val all_messages = new Event_Bus[Isabelle_Process.Message]  // potential bottle-neck
  val trace_events = new Event_Bus[Simplifier_Trace.Event.type]


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
    doc_blobs: Document.Blobs,
    text_edits: List[Document.Edit_Text],
    version_result: Promise[Document.Version])

  private val (_, change_parser) = Simple_Thread.actor("change_parser", daemon = true)
  {
    var finished = false
    while (!finished) {
      receive {
        case Stop => finished = true; reply(())

        case Text_Edits(previous, doc_blobs, text_edits, version_result) =>
          val prev = previous.get_finished
          val (syntax_changed, doc_edits, version) =
            Timing.timeit("text_edits", timing) {
              resources.text_edits(reparse_limit, prev, doc_blobs, text_edits)
            }
          version_result.fulfill(version)
          sender ! Change(doc_blobs, syntax_changed, doc_edits, prev, version)

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
    if (version.is_init) resources.base_syntax
    else version.syntax
  }

  def snapshot(name: Document.Node.Name = Document.Node.Name.empty,
      pending_edits: List[Text.Edit] = Nil): Document.Snapshot =
    global_state().snapshot(name, pending_edits)


  /* protocol handlers */

  @volatile private var _protocol_handlers = new Session.Protocol_Handlers()

  def protocol_handler(name: String): Option[Session.Protocol_Handler] =
    _protocol_handlers.get(name)


  /* theory files */

  def header_edit(name: Document.Node.Name, header: Document.Node.Header): Document.Edit_Text =
  {
    val header1 =
      if (resources.loaded_theories(name.theory))
        header.error("Cannot update finished theory " + quote(name.theory))
      else header
    (name, Document.Node.Deps(header1))
  }


  /* actor messages */

  private case class Start(args: List[String])
  private case class Cancel_Exec(exec_id: Document_ID.Exec)
  private case class Change(
    doc_blobs: Document.Blobs,
    syntax_changed: Boolean,
    doc_edits: List[Document.Edit_Command],
    previous: Document.Version,
    version: Document.Version)
  private case class Protocol_Command(name: String, args: List[String])
  private case class Messages(msgs: List[Isabelle_Process.Message])
  private case class Update_Options(options: Options)

  private val (_, session_actor) = Simple_Thread.actor("session_actor", daemon = true)
  {
    val this_actor = self

    var prune_next = System.currentTimeMillis() + prune_delay.ms


    /* buffered prover messages */

    object receiver
    {
      private var buffer = new mutable.ListBuffer[Isabelle_Process.Message]

      private def flush(): Unit = synchronized {
        if (!buffer.isEmpty) {
          val msgs = buffer.toList
          this_actor ! Messages(msgs)
          buffer = new mutable.ListBuffer[Isabelle_Process.Message]
        }
      }
      def invoke(msg: Isabelle_Process.Message): Unit = synchronized {
        msg match {
          case _: Isabelle_Process.Input =>
            buffer += msg
          case output: Isabelle_Process.Protocol_Output if output.properties == Markup.Flush =>
            flush()
          case output: Isabelle_Process.Output =>
            buffer += msg
            if (output.is_syslog)
              syslog >> (queue =>
                {
                  val queue1 = queue.enqueue(output.message)
                  if (queue1.length > syslog_limit) queue1.dequeue._2 else queue1
                })
        }
      }

      private val timer = new Timer("session_actor.receiver", true)
      timer.schedule(new TimerTask { def run = flush }, message_delay.ms, message_delay.ms)

      def cancel() { timer.cancel() }
    }

    var prover: Option[Session.Prover] = None


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


    /* raw edits */

    def handle_raw_edits(doc_blobs: Document.Blobs, edits: List[Document.Edit_Text])
    //{{{
    {
      prover.get.discontinue_execution()

      val previous = global_state().history.tip.version
      val version = Future.promise[Document.Version]
      val change = global_state >>> (_.continue_history(previous, edits, version))

      raw_edits.event(Session.Raw_Edits(doc_blobs, edits))
      change_parser ! Text_Edits(previous, doc_blobs, edits, version)
    }
    //}}}


    /* resulting changes */

    def handle_change(change: Change)
    //{{{
    {
      val Change(doc_blobs, syntax_changed, doc_edits, previous, version) = change

      def id_command(command: Command)
      {
        for {
          digest <- command.blobs_digests
          if !global_state().defined_blob(digest)
        } {
          doc_blobs.get(digest) match {
            case Some(blob) =>
              global_state >> (_.define_blob(digest))
              prover.get.define_blob(blob)
            case None =>
              System.err.println("Missing blob for SHA1 digest " + digest)
          }
        }

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

      if (syntax_changed) resources.syntax_changed()
    }
    //}}}


    /* prover output */

    def handle_output(output: Isabelle_Process.Output)
    //{{{
    {
      def bad_output()
      {
        if (verbose)
          System.err.println("Ignoring prover output: " + output.message.toString)
      }

      def accumulate(state_id: Document_ID.Generic, message: XML.Elem)
      {
        try {
          val st = global_state >>> (_.accumulate(state_id, message))
          delay_commands_changed.invoke(false, List(st.command))
        }
        catch {
          case _: Document.State.Fail => bad_output()
        }
      }

      output match {
        case msg: Isabelle_Process.Protocol_Output =>
          val handled = _protocol_handlers.invoke(msg)
          if (!handled) {
            msg.properties match {
              case Markup.Protocol_Handler(name) =>
                _protocol_handlers = _protocol_handlers.add(prover.get, name)

              case Protocol.Command_Timing(state_id, timing) =>
                val message = XML.elem(Markup.STATUS, List(XML.Elem(Markup.Timing(timing), Nil)))
                accumulate(state_id, prover.get.xml_cache.elem(message))

              case Markup.Assign_Update =>
                msg.text match {
                  case Protocol.Assign_Update(id, update) =>
                    try {
                      val cmds = global_state >>> (_.assign(id, update))
                      delay_commands_changed.invoke(true, cmds)
                    }
                    catch { case _: Document.State.Fail => bad_output() }
                  case _ => bad_output()
                }
                // FIXME separate timeout event/message!?
                if (prover.isDefined && System.currentTimeMillis() > prune_next) {
                  val old_versions = global_state >>> (_.prune_history(prune_size))
                  if (!old_versions.isEmpty) prover.get.remove_versions(old_versions)
                  prune_next = System.currentTimeMillis() + prune_delay.ms
                }

              case Markup.Removed_Versions =>
                msg.text match {
                  case Protocol.Removed(removed) =>
                    try {
                      global_state >> (_.removed_versions(removed))
                    }
                    catch { case _: Document.State.Fail => bad_output() }
                  case _ => bad_output()
                }

              case Markup.ML_Statistics(props) =>
                statistics.event(Session.Statistics(props))

              case Markup.Task_Statistics(props) =>
                // FIXME

              case _ => bad_output()
            }
          }
        case _ =>
          output.properties match {
            case Position.Id(state_id) =>
              accumulate(state_id, output.message)

            case _ if output.is_init =>
              phase = Session.Ready

            case Markup.Return_Code(rc) if output.is_exit =>
              if (rc == 0) phase = Session.Inactive
              else phase = Session.Failed

            case _ => raw_output_messages.event(output)
          }
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
            _protocol_handlers = _protocol_handlers.stop(prover.get)
            global_state >> (_ => Document.State.init)  // FIXME event bus!?
            phase = Session.Shutdown
            prover.get.terminate
            prover = None
            phase = Session.Inactive
          }
          finished = true
          receiver.cancel()
          reply(())

        case Update_Options(options) if prover.isDefined =>
          if (is_ready) {
            prover.get.options(options)
            handle_raw_edits(Document.Blobs.empty, Nil)
          }
          global_options.event(Session.Global_Options(options))
          reply(())

        case Cancel_Exec(exec_id) if prover.isDefined =>
          prover.get.cancel_exec(exec_id)

        case Session.Raw_Edits(doc_blobs, edits) if prover.isDefined =>
          handle_raw_edits(doc_blobs, edits)
          reply(())

        case Session.Dialog_Result(id, serial, result) if prover.isDefined =>
          prover.get.dialog_result(serial, result)
          handle_output(new Isabelle_Process.Output(Protocol.Dialog_Result(id, serial, result)))

        case Protocol_Command(name, args) if prover.isDefined =>
          prover.get.protocol_command(name, args:_*)

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
  {
    session_actor ! Start(args)
  }

  def stop()
  {
    commands_changed_buffer !? Stop
    change_parser !? Stop
    session_actor !? Stop
  }

  def protocol_command(name: String, args: String*)
  { session_actor ! Protocol_Command(name, args.toList) }

  def cancel_exec(exec_id: Document_ID.Exec) { session_actor ! Cancel_Exec(exec_id) }

  def update(doc_blobs: Document.Blobs, edits: List[Document.Edit_Text])
  { if (!edits.isEmpty) session_actor !? Session.Raw_Edits(doc_blobs, edits) }

  def update_options(options: Options)
  { session_actor !? Update_Options(options) }

  def dialog_result(id: Document_ID.Generic, serial: Long, result: String)
  { session_actor ! Session.Dialog_Result(id, serial, result) }
}
