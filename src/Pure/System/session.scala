/*  Title:      Pure/System/session.scala
    Author:     Makarius
    Options:    :folding=explicit:collapseFolds=1:

Main Isabelle/Scala session, potentially with running prover process.
*/

package isabelle

import java.lang.System

import scala.actors.TIMEOUT
import scala.actors.Actor
import scala.actors.Actor._


object Session
{
  /* file store */

  abstract class File_Store
  {
    def append(master_dir: String, path: Path): String
    def require(file: String): Unit
  }


  /* events */

  //{{{
  case object Global_Settings
  case object Perspective
  case object Assignment
  case class Commands_Changed(set: Set[Command])

  sealed abstract class Phase
  case object Inactive extends Phase
  case object Startup extends Phase  // transient
  case object Failed extends Phase
  case object Ready extends Phase
  case object Shutdown extends Phase  // transient
  //}}}
}


class Session(val file_store: Session.File_Store)
{
  /* real time parameters */  // FIXME properties or settings (!?)

  val input_delay = Time.seconds(0.3)  // user input (e.g. text edits, cursor movement)
  val output_delay = Time.seconds(0.1)  // prover output (markup, common messages)
  val update_delay = Time.seconds(0.5)  // GUI layout updates


  /* pervasive event buses */

  val global_settings = new Event_Bus[Session.Global_Settings.type]
  val perspective = new Event_Bus[Session.Perspective.type]
  val assignments = new Event_Bus[Session.Assignment.type]
  val commands_changed = new Event_Bus[Session.Commands_Changed]
  val phase_changed = new Event_Bus[Session.Phase]
  val raw_messages = new Event_Bus[Isabelle_Process.Message]



  /** buffered command changes (delay_first discipline) **/

  //{{{
  private case object Stop

  private val (_, command_change_buffer) =
    Simple_Thread.actor("command_change_buffer", daemon = true)
  {
    var changed: Set[Command] = Set()
    var flush_time: Option[Long] = None

    def flush_timeout: Long =
      flush_time match {
        case None => 5000L
        case Some(time) => (time - System.currentTimeMillis()) max 0
      }

    def flush()
    {
      if (!changed.isEmpty) commands_changed.event(Session.Commands_Changed(changed))
      changed = Set()
      flush_time = None
    }

    def invoke()
    {
      val now = System.currentTimeMillis()
      flush_time match {
        case None => flush_time = Some(now + output_delay.ms)
        case Some(time) => if (now >= time) flush()
      }
    }

    var finished = false
    while (!finished) {
      receiveWithin(flush_timeout) {
        case command: Command => changed += command; invoke()
        case TIMEOUT => flush()
        case Stop => finished = true; reply(())
        case bad => System.err.println("command_change_buffer: ignoring bad message " + bad)
      }
    }
  }
  //}}}



  /** main protocol actor **/

  /* global state */

  @volatile var verbose: Boolean = false

  @volatile private var loaded_theories: Set[String] = Set()

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

  private val global_state = new Volatile(Document.State.init)
  def current_state(): Document.State = global_state()

  def snapshot(name: String, pending_edits: List[Text.Edit]): Document.Snapshot =
    global_state().snapshot(name, pending_edits)


  /* theory files */

  val thy_load = new Thy_Load
  {
    override def is_loaded(name: String): Boolean =
      loaded_theories.contains(name)

    override def check_thy(dir: Path, name: String): (String, Thy_Header) =
    {
      val file = Isabelle_System.platform_file(dir + Thy_Header.thy_path(name))
      if (!file.exists || !file.isFile) error("No such file: " + quote(file.toString))
      val text = Standard_System.read_file(file)
      val header = Thy_Header.read(text)
      (text, header)
    }
  }

  val thy_info = new Thy_Info(thy_load)

  def header_edit(name: String, master_dir: String,
    header: Document.Node_Header): Document.Edit_Text =
  {
    def norm_import(s: String): String =
    {
      val thy_name = Thy_Header.base_name(s)
      if (thy_load.is_loaded(thy_name)) thy_name
      else file_store.append(master_dir, Thy_Header.thy_path(Path.explode(s)))
    }
    def norm_use(s: String): String =
      file_store.append(master_dir, Path.explode(s))

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
  private case object Interrupt
  private case class Init_Node(name: String, master_dir: String,
    header: Document.Node_Header, perspective: Text.Perspective, text: String)
  private case class Edit_Node(name: String, master_dir: String,
    header: Document.Node_Header, perspective: Text.Perspective, edits: List[Text.Edit])
  private case class Change_Node(
    name: String,
    doc_edits: List[Document.Edit_Command],
    previous: Document.Version,
    version: Document.Version)

  private val (_, session_actor) = Simple_Thread.actor("session_actor", daemon = true)
  {
    val this_actor = self
    var prover: Option[Isabelle_Process with Isar_Document] = None


    /* perspective */

    def update_perspective(name: String, text_perspective: Text.Perspective)
    {
      val previous = global_state().history.tip.version.get_finished
      val (perspective, version) = Thy_Syntax.edit_perspective(previous, name, text_perspective)

      val text_edits: List[Document.Edit_Text] =
        List((name, Document.Node.Perspective(text_perspective)))
      val change =
        global_state.change_yield(
          _.extend_history(Future.value(previous), text_edits, Future.value(version)))

      val assignment = global_state().the_assignment(previous).get_finished
      global_state.change(_.define_version(version, assignment))
      global_state.change_yield(_.assign(version.id, Nil))

      prover.get.update_perspective(previous.id, version.id, name, perspective)
    }


    /* incoming edits */

    def handle_edits(name: String, master_dir: String,
        header: Document.Node_Header, edits: List[Document.Node.Edit[Text.Edit, Text.Perspective]])
    //{{{
    {
      val syntax = current_syntax()
      val previous = global_state().history.tip.version

      val text_edits = header_edit(name, master_dir, header) :: edits.map(edit => (name, edit))
      val result = Future.fork { Thy_Syntax.text_edits(syntax, previous.join, text_edits) }
      val change =
        global_state.change_yield(_.extend_history(previous, text_edits, result.map(_._2)))

      result.map {
        case (doc_edits, _) =>
          assignments.await { global_state().is_assigned(previous.get_finished) }
          this_actor ! Change_Node(name, doc_edits, previous.join, change.version.join)
      }
    }
    //}}}


    /* exec state assignment */

    def handle_assign(id: Document.Version_ID, edits: List[(Document.Command_ID, Document.Exec_ID)])
    //{{{
    {
      val cmds = global_state.change_yield(_.assign(id, edits))
      for (cmd <- cmds) command_change_buffer ! cmd
      assignments.event(Session.Assignment)
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

      var former_assignment = global_state().the_assignment(previous).get_finished
      for {
        (name, Document.Node.Edits(cmd_edits)) <- doc_edits  // FIXME proper coverage!?
        (prev, None) <- cmd_edits
        removed <- previous.nodes(name).commands.get_after(prev)
      } former_assignment -= removed

      def id_command(command: Command)
      {
        if (global_state().lookup_command(command.id).isEmpty) {
          global_state.change(_.define_command(command))
          prover.get.define_command(command.id, Symbol.encode(command.source))
        }
      }
      doc_edits foreach {
        case (_, edit) =>
          edit foreach { case (c1, c2) => c1 foreach id_command; c2 foreach id_command }
      }

      global_state.change(_.define_version(version, former_assignment))
      prover.get.edit_version(previous.id, version.id, doc_edits)
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
            command_change_buffer ! st.command
          }
          catch {
            case _: Document.State.Fail => bad_result(result)
          }
        case Markup.Invoke_Scala(name, id) if result.is_raw =>
          Future.fork {
            val arg = XML.content(result.body).mkString
            val (tag, res) = Invoke_Scala.method(name, arg)
            prover.get.invoke_scala(id, tag, res)
          }
        case Markup.Cancel_Scala(id) =>
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
              case List(Isar_Document.Assign(id, edits)) =>
                try { handle_assign(id, edits) }
                catch { case _: Document.State.Fail => bad_result(result) }
              case List(Keyword.Command_Decl(name, kind)) => syntax += (name, kind)
              case List(Keyword.Keyword_Decl(name)) => syntax += name
              case List(Thy_Info.Loaded_Theory(name)) => loaded_theories += name
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
      receive {
        case Start(timeout, args) if prover.isEmpty =>
          if (phase == Session.Inactive || phase == Session.Failed) {
            phase = Session.Startup
            prover = Some(new Isabelle_Process(timeout, this_actor, args:_*) with Isar_Document)
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
          reply(())

        case Interrupt if prover.isDefined =>
          prover.get.interrupt

        case Init_Node(name, master_dir, header, perspective, text) if prover.isDefined =>
          // FIXME compare with existing node
          handle_edits(name, master_dir, header,
            List(Document.Node.Clear(),
              Document.Node.Edits(List(Text.Edit.insert(0, text))),
              Document.Node.Perspective(perspective)))
          reply(())

        case Edit_Node(name, master_dir, header, perspective, text_edits) if prover.isDefined =>
          if (text_edits.isEmpty && global_state().tip_stable)
            update_perspective(name, perspective)
          else
            handle_edits(name, master_dir, header,
              List(Document.Node.Edits(text_edits), Document.Node.Perspective(perspective)))
          reply(())

        case change: Change_Node if prover.isDefined =>
          handle_change(change)

        case input: Isabelle_Process.Input =>
          raw_messages.event(input)

        case result: Isabelle_Process.Result =>
          handle_result(result)
          raw_messages.event(result)

        case bad => System.err.println("session_actor: ignoring bad message " + bad)
      }
    }
    //}}}
  }


  /* actions */

  def start(timeout: Time, args: List[String]) { session_actor ! Start(timeout, args) }

  def stop() { command_change_buffer !? Stop; session_actor !? Stop }

  def interrupt() { session_actor ! Interrupt }

  // FIXME simplify signature
  def init_node(name: String, master_dir: String,
    header: Document.Node_Header, perspective: Text.Perspective, text: String)
  { session_actor !? Init_Node(name, master_dir, header, perspective, text) }

  // FIXME simplify signature
  def edit_node(name: String, master_dir: String, header: Document.Node_Header,
    perspective: Text.Perspective, edits: List[Text.Edit])
  { session_actor !? Edit_Node(name, master_dir, header, perspective, edits) }
}
