/*  Title:      Pure/System/session.scala
    Author:     Makarius
    Options:    :folding=explicit:collapseFolds=1:

Main Isabelle/Scala session, potentially with running prover process.
*/

package isabelle


import java.lang.System
import java.util.{Timer, TimerTask}

import scala.collection.mutable
import scala.actors.TIMEOUT
import scala.actors.Actor._


object Session
{
  /* events */

  //{{{
  case object Global_Settings
  case object Caret_Focus
  case class Commands_Changed(nodes: Set[Document.Node.Name], commands: Set[Command])

  sealed abstract class Phase
  case object Inactive extends Phase
  case object Startup extends Phase  // transient
  case object Failed extends Phase
  case object Ready extends Phase
  case object Shutdown extends Phase  // transient
  //}}}
}


class Session(thy_load: Thy_Load = new Thy_Load)
{
  /* real time parameters */  // FIXME properties or settings (!?)

  val message_delay = Time.seconds(0.01)  // prover messages
  val input_delay = Time.seconds(0.3)  // user input (e.g. text edits, cursor movement)
  val output_delay = Time.seconds(0.1)  // prover output (markup, common messages)
  val update_delay = Time.seconds(0.5)  // GUI layout updates
  val load_delay = Time.seconds(0.5)  // file load operations (new buffers etc.)
  val prune_delay = Time.seconds(60.0)  // prune history -- delete old versions
  val prune_size = 0  // size of retained history


  /* pervasive event buses */

  val global_settings = new Event_Bus[Session.Global_Settings.type]
  val caret_focus = new Event_Bus[Session.Caret_Focus.type]
  val commands_changed = new Event_Bus[Session.Commands_Changed]
  val phase_changed = new Event_Bus[Session.Phase]
  val syslog_messages = new Event_Bus[Isabelle_Process.Result]
  val raw_output_messages = new Event_Bus[Isabelle_Process.Result]
  val protocol_messages = new Event_Bus[Isabelle_Process.Message]  // potential bottle-neck



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
    syntax: Outer_Syntax,
    name: Document.Node.Name,
    previous: Future[Document.Version],
    text_edits: List[Document.Edit_Text],
    version_result: Promise[Document.Version])

  private val (_, change_parser) = Simple_Thread.actor("change_parser", daemon = true)
  {
    var finished = false
    while (!finished) {
      receive {
        case Stop => finished = true; reply(())

        case Text_Edits(syntax, name, previous, text_edits, version_result) =>
          val prev = previous.get_finished
          val (doc_edits, version) = Thy_Syntax.text_edits(syntax, prev, text_edits)
          version_result.fulfill(version)
          sender ! Change_Node(name, doc_edits, prev, version)

        case bad => System.err.println("change_parser: ignoring bad message " + bad)
      }
    }
  }
  //}}}


  /** main protocol actor **/

  /* global state */

  @volatile var verbose: Boolean = false

  @volatile private var syntax = new Outer_Syntax
  def current_syntax(): Outer_Syntax = syntax

  @volatile private var reverse_syslog = List[XML.Elem]()
  def syslog(): String = reverse_syslog.reverse.map(msg => XML.content(msg).mkString).mkString("\n")

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

  def snapshot(name: Document.Node.Name = Document.Node.Name.empty,
      pending_edits: List[Text.Edit] = Nil): Document.Snapshot =
    global_state().snapshot(name, pending_edits)


  /* theory files */

  def header_edit(name: Document.Node.Name, header: Document.Node_Header): Document.Edit_Text =
  {
    def norm_import(s: String): String =
    {
      val thy_name = Thy_Header.base_name(s)
      if (thy_load.is_loaded(thy_name)) thy_name
      else thy_load.append(name.dir, Thy_Header.thy_path(Path.explode(s)))
    }
    def norm_use(s: String): String = thy_load.append(name.dir, Path.explode(s))

    val header1: Document.Node_Header =
      header match {
        case Exn.Res(Thy_Header(thy_name, _, _))
        if (thy_load.is_loaded(thy_name)) =>
          Exn.Exn(ERROR("Attempt to update loaded theory " + quote(thy_name)))
        case _ => Document.Node.norm_header(norm_import, norm_use, header)
      }
    (name, Document.Node.Header(header1))
  }


  /* actor messages */

  private case class Start(timeout: Time, args: List[String])
  private case object Cancel_Execution
  private case class Init_Node(name: Document.Node.Name,
    header: Document.Node_Header, perspective: Text.Perspective, text: String)
  private case class Edit_Node(name: Document.Node.Name,
    header: Document.Node_Header, perspective: Text.Perspective, edits: List[Text.Edit])
  private case class Change_Node(
    name: Document.Node.Name,
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
          case result: Isabelle_Process.Result if result.is_raw => flush()
          case _ =>
        }
      }

      private val timer = new Timer("session_actor.receiver", true)
      timer.schedule(new TimerTask { def run = flush }, message_delay.ms, message_delay.ms)

      def cancel() { timer.cancel() }
    }

    var prover: Option[Isabelle_Process with Protocol] = None


    /* delayed command changes */

    object commands_changed_delay
    {
      private var changed_nodes: Set[Document.Node.Name] = Set.empty
      private var changed_commands: Set[Command] = Set.empty
      private def changed: Boolean = !changed_nodes.isEmpty || !changed_commands.isEmpty

      private var flush_time: Option[Long] = None

      def flush_timeout: Long =
        flush_time match {
          case None => 5000L
          case Some(time) => (time - System.currentTimeMillis()) max 0
        }

      def flush()
      {
        if (changed)
          commands_changed_buffer ! Session.Commands_Changed(changed_nodes, changed_commands)
        changed_nodes = Set.empty
        changed_commands = Set.empty
        flush_time = None
      }

      def invoke(command: Command)
      {
        changed_nodes += command.node_name
        changed_commands += command
        val now = System.currentTimeMillis()
        flush_time match {
          case None => flush_time = Some(now + output_delay.ms)
          case Some(time) => if (now >= time) flush()
        }
      }
    }


    /* perspective */

    def update_perspective(name: Document.Node.Name, text_perspective: Text.Perspective)
    {
      val previous = global_state().tip_version
      val (perspective, version) = Thy_Syntax.edit_perspective(previous, name, text_perspective)

      val text_edits: List[Document.Edit_Text] =
        List((name, Document.Node.Perspective(text_perspective)))
      val change =
        global_state.change_yield(
          _.continue_history(Future.value(previous), text_edits, Future.value(version)))

      val assignment = global_state().the_assignment(previous).check_finished
      global_state.change(_.define_version(version, assignment))
      global_state.change_yield(_.assign(version.id, Document.no_assign))

      prover.get.update_perspective(previous.id, version.id, name, perspective)
    }


    /* incoming edits */

    def handle_edits(name: Document.Node.Name,
        header: Document.Node_Header, edits: List[Document.Node.Edit[Text.Edit, Text.Perspective]])
    //{{{
    {
      val syntax = current_syntax()
      val previous = global_state().history.tip.version

      prover.get.cancel_execution()

      val text_edits = header_edit(name, header) :: edits.map(edit => (name, edit))
      val version = Future.promise[Document.Version]
      val change = global_state.change_yield(_.continue_history(previous, text_edits, version))

      change_parser ! Text_Edits(syntax, name, previous, text_edits, version)
    }
    //}}}


    /* exec state assignment */

    def handle_assign(id: Document.Version_ID, assign: Document.Assign)
    //{{{
    {
      val cmds = global_state.change_yield(_.assign(id, assign))
      for (cmd <- cmds) commands_changed_delay.invoke(cmd)
    }
    //}}}


    /* removed versions */

    def handle_removed(removed: List[Document.Version_ID])
    //{{{
    {
      global_state.change(_.removed_versions(removed))
    }
    //}}}


    /* resulting changes */

    def handle_change(change: Change_Node)
    //{{{
    {
      val previous = change.previous
      val version = change.version
      val name = change.name
      val doc_edits = change.doc_edits

      def id_command(command: Command)
      {
        if (!global_state().defined_command(command.id)) {
          global_state.change(_.define_command(command))
          prover.get.define_command(command)
        }
      }
      doc_edits foreach {
        case (_, edit) =>
          edit foreach { case (c1, c2) => c1 foreach id_command; c2 foreach id_command }
      }

      val assignment = global_state().the_assignment(previous).check_finished
      global_state.change(_.define_version(version, assignment))
      prover.get.update(previous.id, version.id, doc_edits)
    }
    //}}}


    /* prover results */

    def handle_result(result: Isabelle_Process.Result)
    //{{{
    {
      def bad_result(result: Isabelle_Process.Result)
      {
        if (verbose)
          System.err.println("Ignoring prover result: " + result.message.toString)
      }

      result.properties match {
        case Position.Id(state_id) if !result.is_raw =>
          try {
            val st = global_state.change_yield(_.accumulate(state_id, result.message))
            commands_changed_delay.invoke(st.command)
          }
          catch {
            case _: Document.State.Fail => bad_result(result)
          }
        case Isabelle_Markup.Assign_Execs if result.is_raw =>
          XML.content(result.body).mkString match {
            case Protocol.Assign(id, assign) =>
              try { handle_assign(id, assign) }
              catch { case _: Document.State.Fail => bad_result(result) }
            case _ => bad_result(result)
          }
          // FIXME separate timeout event/message!?
          if (prover.isDefined && System.currentTimeMillis() > prune_next) {
            val old_versions = global_state.change_yield(_.prune_history(prune_size))
            if (!old_versions.isEmpty) prover.get.remove_versions(old_versions)
            prune_next = System.currentTimeMillis() + prune_delay.ms
          }
        case Isabelle_Markup.Removed_Versions if result.is_raw =>
          XML.content(result.body).mkString match {
            case Protocol.Removed(removed) =>
              try { handle_removed(removed) }
              catch { case _: Document.State.Fail => bad_result(result) }
            case _ => bad_result(result)
          }
        case Isabelle_Markup.Invoke_Scala(name, id) if result.is_raw =>
          Future.fork {
            val arg = XML.content(result.body).mkString
            val (tag, res) = Invoke_Scala.method(name, arg)
            prover.get.invoke_scala(id, tag, res)
          }
        case Isabelle_Markup.Cancel_Scala(id) =>
          System.err.println("cancel_scala " + id)  // FIXME cancel JVM task
        case _ =>
          if (result.is_syslog) {
            reverse_syslog ::= result.message
            if (result.is_ready) {
              // FIXME move to ML side (!?)
              syntax += ("hence", Keyword.PRF_ASM_GOAL, "then have")
              syntax += ("thus", Keyword.PRF_ASM_GOAL, "then show")
              phase = Session.Ready
            }
            else if (result.is_exit && phase == Session.Startup) phase = Session.Failed
            else if (result.is_exit) phase = Session.Inactive
          }
          else if (result.is_stdout) { }
          else if (result.is_status) {
            result.body match {
              case List(Keyword.Command_Decl(name, kind)) => syntax += (name, kind)
              case List(Keyword.Keyword_Decl(name)) => syntax += name
              case List(Thy_Info.Loaded_Theory(name)) => thy_load.register_thy(name)
              case _ => bad_result(result)
            }
          }
          else bad_result(result)
      }
    }
    //}}}


    /* main loop */

    //{{{
    var finished = false
    while (!finished) {
      receiveWithin(commands_changed_delay.flush_timeout) {
        case TIMEOUT => commands_changed_delay.flush()

        case Start(timeout, args) if prover.isEmpty =>
          if (phase == Session.Inactive || phase == Session.Failed) {
            phase = Session.Startup
            prover = Some(new Isabelle_Process(timeout, receiver.invoke _, args) with Protocol)
          }

        case Stop =>
          if (phase == Session.Ready) {
            global_state.change(_ => Document.State.init)  // FIXME event bus!?
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

        case Init_Node(name, header, perspective, text) if prover.isDefined =>
          // FIXME compare with existing node
          handle_edits(name, header,
            List(Document.Node.Clear(),
              Document.Node.Edits(List(Text.Edit.insert(0, text))),
              Document.Node.Perspective(perspective)))
          reply(())

        case Edit_Node(name, header, perspective, text_edits) if prover.isDefined =>
          if (text_edits.isEmpty && global_state().tip_stable &&
              perspective.range.stop <= global_state().last_exec_offset(name))
            update_perspective(name, perspective)
          else
            handle_edits(name, header,
              List(Document.Node.Edits(text_edits), Document.Node.Perspective(perspective)))
          reply(())

        case Messages(msgs) =>
          msgs foreach {
            case input: Isabelle_Process.Input =>
              protocol_messages.event(input)

            case result: Isabelle_Process.Result =>
              handle_result(result)
              if (result.is_syslog) syslog_messages.event(result)
              if (result.is_stdout || result.is_stderr) raw_output_messages.event(result)
              protocol_messages.event(result)
          }

        case change: Change_Node
        if prover.isDefined && global_state().is_assigned(change.previous) =>
          handle_change(change)

        case bad if !bad.isInstanceOf[Change_Node] =>
          System.err.println("session_actor: ignoring bad message " + bad)
      }
    }
    //}}}
  }


  /* actions */

  def start(timeout: Time, args: List[String])
  { session_actor ! Start(timeout, args) }

  def start(args: List[String]) { start (Time.seconds(25), args) }

  def stop() { commands_changed_buffer !? Stop; change_parser !? Stop; session_actor !? Stop }

  def cancel_execution() { session_actor ! Cancel_Execution }

  def init_node(name: Document.Node.Name,
    header: Document.Node_Header, perspective: Text.Perspective, text: String)
  { session_actor !? Init_Node(name, header, perspective, text) }

  def edit_node(name: Document.Node.Name,
    header: Document.Node_Header, perspective: Text.Perspective, edits: List[Text.Edit])
  { session_actor !? Edit_Node(name, header, perspective, edits) }
}
