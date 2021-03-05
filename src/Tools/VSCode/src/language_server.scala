/*  Title:      Tools/VSCode/src/language_server.scala
    Author:     Makarius

Server for VS Code Language Server Protocol 2.0/3.0, see also
https://github.com/Microsoft/language-server-protocol
https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md

PIDE protocol extensions depend on system option "vscode_pide_extensions".
*/

package isabelle.vscode


import isabelle._

import java.io.{PrintStream, OutputStream, File => JFile}

import scala.annotation.tailrec
import scala.collection.mutable


object Language_Server
{
  type Editor = isabelle.Editor[Unit]


  /* Isabelle tool wrapper */

  private lazy val default_logic = Isabelle_System.getenv("ISABELLE_LOGIC")

  val isabelle_tool =
    Isabelle_Tool("vscode_server", "VSCode Language Server for PIDE", Scala_Project.here, args =>
    {
      try {
        var logic_ancestor: Option[String] = None
        var log_file: Option[Path] = None
        var logic_requirements = false
        var dirs: List[Path] = Nil
        var include_sessions: List[String] = Nil
        var logic = default_logic
        var modes: List[String] = Nil
        var options = Options.init()
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle vscode_server [OPTIONS]

  Options are:
    -A NAME      ancestor session for option -R (default: parent)
    -L FILE      logging on FILE
    -R NAME      build image with requirements from other sessions
    -d DIR       include session directory
    -i NAME      include session in name-space of theories
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(default_logic) + """)
    -m MODE      add print mode for output
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose logging

  Run the VSCode Language Server protocol (JSON RPC) over stdin/stdout.
""",
          "A:" -> (arg => logic_ancestor = Some(arg)),
          "L:" -> (arg => log_file = Some(Path.explode(File.standard_path(arg)))),
          "R:" -> (arg => { logic = arg; logic_requirements = true }),
          "d:" -> (arg => dirs = dirs ::: List(Path.explode(File.standard_path(arg)))),
          "i:" -> (arg => include_sessions = include_sessions ::: List(arg)),
          "l:" -> (arg => logic = arg),
          "m:" -> (arg => modes = arg :: modes),
          "o:" -> (arg => options = options + arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val log = Logger.make(log_file)
        val channel = new Channel(System.in, System.out, log, verbose)
        val server =
          new Language_Server(channel, options, session_name = logic, session_dirs = dirs,
            include_sessions = include_sessions, session_ancestor = logic_ancestor,
            session_requirements = logic_requirements, modes = modes, log = log)

        // prevent spurious garbage on the main protocol channel
        val orig_out = System.out
        try {
          System.setOut(new PrintStream(new OutputStream { def write(n: Int): Unit = {} }))
          server.start()
        }
        finally { System.setOut(orig_out) }
      }
      catch {
        case exn: Throwable =>
          val channel = new Channel(System.in, System.out, No_Logger)
          channel.error_message(Exn.message(exn))
          throw(exn)
      }
    })
}

class Language_Server(
  val channel: Channel,
  options: Options,
  session_name: String = Language_Server.default_logic,
  session_dirs: List[Path] = Nil,
  include_sessions: List[String] = Nil,
  session_ancestor: Option[String] = None,
  session_requirements: Boolean = false,
  modes: List[String] = Nil,
  log: Logger = No_Logger)
{
  server =>


  /* prover session */

  private val session_ = Synchronized(None: Option[Session])
  def session: Session = session_.value getOrElse error("Server inactive")
  def resources: VSCode_Resources = session.resources.asInstanceOf[VSCode_Resources]

  def rendering_offset(node_pos: Line.Node_Position): Option[(VSCode_Rendering, Text.Offset)] =
    for {
      model <- resources.get_model(new JFile(node_pos.name))
      rendering = model.rendering()
      offset <- model.content.doc.offset(node_pos.pos)
    } yield (rendering, offset)

  private val dynamic_output = Dynamic_Output(server)


  /* input from client or file-system */

  private val delay_input: Delay =
    Delay.last(options.seconds("vscode_input_delay"), channel.Error_Logger)
    { resources.flush_input(session, channel) }

  private val delay_load: Delay =
    Delay.last(options.seconds("vscode_load_delay"), channel.Error_Logger) {
      val (invoke_input, invoke_load) =
        resources.resolve_dependencies(session, editor, file_watcher)
      if (invoke_input) delay_input.invoke()
      if (invoke_load) delay_load.invoke()
    }

  private val file_watcher =
    File_Watcher(sync_documents, options.seconds("vscode_load_delay"))

  private def close_document(file: JFile): Unit =
  {
    if (resources.close_model(file)) {
      file_watcher.register_parent(file)
      sync_documents(Set(file))
      delay_input.invoke()
      delay_output.invoke()
    }
  }

  private def sync_documents(changed: Set[JFile]): Unit =
  {
    resources.sync_models(changed)
    delay_input.invoke()
    delay_output.invoke()
  }

  private def change_document(
    file: JFile, version: Long, changes: List[LSP.TextDocumentChange]): Unit =
  {
    val norm_changes = new mutable.ListBuffer[LSP.TextDocumentChange]
    @tailrec def norm(chs: List[LSP.TextDocumentChange]): Unit =
    {
      if (chs.nonEmpty) {
        val (full_texts, rest1) = chs.span(_.range.isEmpty)
        val (edits, rest2) = rest1.span(_.range.nonEmpty)
        norm_changes ++= full_texts
        norm_changes ++= edits.sortBy(_.range.get.start)(Line.Position.Ordering).reverse
        norm(rest2)
      }
    }
    norm(changes)
    norm_changes.foreach(change =>
      resources.change_model(session, editor, file, version, change.text, change.range))

    delay_input.invoke()
    delay_output.invoke()
  }


  /* caret handling */

  private val delay_caret_update: Delay =
    Delay.last(options.seconds("vscode_input_delay"), channel.Error_Logger)
    { session.caret_focus.post(Session.Caret_Focus) }

  private def update_caret(caret: Option[(JFile, Line.Position)]): Unit =
  {
    resources.update_caret(caret)
    delay_caret_update.invoke()
    delay_input.invoke()
  }


  /* preview */

  private lazy val preview_panel = new Preview_Panel(resources)

  private lazy val delay_preview: Delay =
    Delay.last(options.seconds("vscode_output_delay"), channel.Error_Logger)
    {
      if (preview_panel.flush(channel)) delay_preview.invoke()
    }

  private def request_preview(file: JFile, column: Int): Unit =
  {
    preview_panel.request(file, column)
    delay_preview.invoke()
  }


  /* output to client */

  private val delay_output: Delay =
    Delay.last(options.seconds("vscode_output_delay"), channel.Error_Logger)
    {
      if (resources.flush_output(channel)) delay_output.invoke()
    }

  def update_output(changed_nodes: Iterable[JFile]): Unit =
  {
    resources.update_output(changed_nodes)
    delay_output.invoke()
  }

  def update_output_visible(): Unit =
  {
    resources.update_output_visible()
    delay_output.invoke()
  }

  private val prover_output =
    Session.Consumer[Session.Commands_Changed](getClass.getName) {
      case changed =>
        update_output(changed.nodes.toList.map(resources.node_file(_)))
    }

  private val syslog_messages =
    Session.Consumer[Prover.Output](getClass.getName) {
      case output => channel.log_writeln(resources.output_xml(output.message))
    }


  /* init and exit */

  def init(id: LSP.Id): Unit =
  {
    def reply_ok(msg: String): Unit =
    {
      channel.write(LSP.Initialize.reply(id, ""))
      channel.writeln(msg)
    }

    def reply_error(msg: String): Unit =
    {
      channel.write(LSP.Initialize.reply(id, msg))
      channel.error_message(msg)
    }

    val try_session =
      try {
        val base_info =
          Sessions.base_info(
            options, session_name, dirs = session_dirs, include_sessions = include_sessions,
            session_ancestor = session_ancestor, session_requirements = session_requirements).check

        def build(no_build: Boolean = false): Build.Results =
          Build.build(options,
            selection = Sessions.Selection.session(base_info.session),
            build_heap = true, no_build = no_build, dirs = session_dirs, infos = base_info.infos)

        if (!build(no_build = true).ok) {
          val start_msg = "Build started for Isabelle/" + base_info.session + " ..."
          val fail_msg = "Session build failed -- prover process remains inactive!"

          val progress = channel.progress(verbose = true)
          progress.echo(start_msg); channel.writeln(start_msg)

          if (!build().ok) { progress.echo(fail_msg); error(fail_msg) }
        }

        val resources = new VSCode_Resources(options, base_info, log)
          {
            override def commit(change: Session.Change): Unit =
              if (change.deps_changed || undefined_blobs(change.version.nodes).nonEmpty)
                delay_load.invoke()
          }

        val session_options = options.bool("editor_output_state") = true
        val session = new Session(session_options, resources)

        Some((base_info, session))
      }
      catch { case ERROR(msg) => reply_error(msg); None }

    for ((base_info, session) <- try_session) {
      session_.change(_ => Some(session))

      session.commands_changed += prover_output
      session.syslog_messages += syslog_messages

      dynamic_output.init()

      try {
        Isabelle_Process(session, options, base_info.sessions_structure, Sessions.store(options),
          modes = modes, logic = base_info.session).await_startup()
        reply_ok("Welcome to Isabelle/" + base_info.session + " (" + Distribution.version + ")")
      }
      catch { case ERROR(msg) => reply_error(msg) }
    }
  }

  def shutdown(id: LSP.Id): Unit =
  {
    def reply(err: String): Unit = channel.write(LSP.Shutdown.reply(id, err))

    session_.change({
      case Some(session) =>
        session.commands_changed -= prover_output
        session.syslog_messages -= syslog_messages

        dynamic_output.exit()

        delay_load.revoke()
        file_watcher.shutdown()
        delay_input.revoke()
        delay_output.revoke()
        delay_caret_update.revoke()
        delay_preview.revoke()

        val result = session.stop()
        if (result.ok) reply("")
        else reply("Prover shutdown failed: " + result.rc)
        None
      case None =>
        reply("Prover inactive")
        None
    })
  }

  def exit(): Unit =
  {
    log("\n")
    sys.exit(if (session_.value.isDefined) 2 else 0)
  }


  /* completion */

  def completion(id: LSP.Id, node_pos: Line.Node_Position): Unit =
  {
    val result =
      (for ((rendering, offset) <- rendering_offset(node_pos))
        yield rendering.completion(node_pos.pos, offset)) getOrElse Nil
    channel.write(LSP.Completion.reply(id, result))
  }


  /* spell-checker dictionary */

  def update_dictionary(include: Boolean, permanent: Boolean): Unit =
  {
    for {
      spell_checker <- resources.spell_checker.get
      caret <- resources.get_caret()
      rendering = caret.model.rendering()
      range = rendering.before_caret_range(caret.offset)
      Text.Info(_, word) <- Spell_Checker.current_word(rendering, range)
    } {
      spell_checker.update(word, include, permanent)
      update_output_visible()
    }
  }

  def reset_dictionary(): Unit =
  {
    for (spell_checker <- resources.spell_checker.get)
    {
      spell_checker.reset()
      update_output_visible()
    }
  }


  /* hover */

  def hover(id: LSP.Id, node_pos: Line.Node_Position): Unit =
  {
    val result =
      for {
        (rendering, offset) <- rendering_offset(node_pos)
        info <- rendering.tooltips(VSCode_Rendering.tooltip_elements, Text.Range(offset, offset + 1))
      } yield {
        val range = rendering.model.content.doc.range(info.range)
        val contents = info.info.map(t => LSP.MarkedString(resources.output_pretty_tooltip(List(t))))
        (range, contents)
      }
    channel.write(LSP.Hover.reply(id, result))
  }


  /* goto definition */

  def goto_definition(id: LSP.Id, node_pos: Line.Node_Position): Unit =
  {
    val result =
      (for ((rendering, offset) <- rendering_offset(node_pos))
        yield rendering.hyperlinks(Text.Range(offset, offset + 1))) getOrElse Nil
    channel.write(LSP.GotoDefinition.reply(id, result))
  }


  /* document highlights */

  def document_highlights(id: LSP.Id, node_pos: Line.Node_Position): Unit =
  {
    val result =
      (for ((rendering, offset) <- rendering_offset(node_pos))
        yield {
          val model = rendering.model
          rendering.caret_focus_ranges(Text.Range(offset, offset + 1), model.content.text_range)
            .map(r => LSP.DocumentHighlight.text(model.content.doc.range(r)))
        }) getOrElse Nil
    channel.write(LSP.DocumentHighlights.reply(id, result))
  }


  /* main loop */

  def start(): Unit =
  {
    log("Server started " + Date.now())

    def handle(json: JSON.T): Unit =
    {
      try {
        json match {
          case LSP.Initialize(id) => init(id)
          case LSP.Initialized(()) =>
          case LSP.Shutdown(id) => shutdown(id)
          case LSP.Exit(()) => exit()
          case LSP.DidOpenTextDocument(file, _, version, text) =>
            change_document(file, version, List(LSP.TextDocumentChange(None, text)))
            delay_load.invoke()
          case LSP.DidChangeTextDocument(file, version, changes) =>
            change_document(file, version, changes)
          case LSP.DidCloseTextDocument(file) => close_document(file)
          case LSP.Completion(id, node_pos) => completion(id, node_pos)
          case LSP.Include_Word(()) => update_dictionary(true, false)
          case LSP.Include_Word_Permanently(()) => update_dictionary(true, true)
          case LSP.Exclude_Word(()) => update_dictionary(false, false)
          case LSP.Exclude_Word_Permanently(()) => update_dictionary(false, true)
          case LSP.Reset_Words(()) => reset_dictionary()
          case LSP.Hover(id, node_pos) => hover(id, node_pos)
          case LSP.GotoDefinition(id, node_pos) => goto_definition(id, node_pos)
          case LSP.DocumentHighlights(id, node_pos) => document_highlights(id, node_pos)
          case LSP.Caret_Update(caret) => update_caret(caret)
          case LSP.State_Init(()) => State_Panel.init(server)
          case LSP.State_Exit(id) => State_Panel.exit(id)
          case LSP.State_Locate(id) => State_Panel.locate(id)
          case LSP.State_Update(id) => State_Panel.update(id)
          case LSP.State_Auto_Update(id, enabled) => State_Panel.auto_update(id, enabled)
          case LSP.Preview_Request(file, column) => request_preview(file, column)
          case LSP.Symbols_Request(()) => channel.write(LSP.Symbols())
          case _ => if (!LSP.ResponseMessage.is_empty(json)) log("### IGNORED")
        }
      }
      catch { case exn: Throwable => channel.log_error_message(Exn.message(exn)) }
    }

    @tailrec def loop(): Unit =
    {
      channel.read() match {
        case Some(json) =>
          json match {
            case bulk: List[_] => bulk.foreach(handle)
            case _ => handle(json)
          }
          loop()
        case None => log("### TERMINATE")
      }
    }
    loop()
  }


  /* abstract editor operations */

  object editor extends Language_Server.Editor
  {
    /* session */

    override def session: Session = server.session
    override def flush(): Unit = resources.flush_input(session, channel)
    override def invoke(): Unit = delay_input.invoke()


    /* current situation */

    override def current_node(context: Unit): Option[Document.Node.Name] =
      resources.get_caret().map(_.model.node_name)
    override def current_node_snapshot(context: Unit): Option[Document.Snapshot] =
      resources.get_caret().map(_.model.snapshot())

    override def node_snapshot(name: Document.Node.Name): Document.Snapshot =
    {
      resources.get_model(name) match {
        case Some(model) => model.snapshot()
        case None => session.snapshot(name)
      }
    }

    def current_command(snapshot: Document.Snapshot): Option[Command] =
    {
      resources.get_caret() match {
        case Some(caret) => snapshot.current_command(caret.node_name, caret.offset)
        case None => None
      }
    }
    override def current_command(context: Unit, snapshot: Document.Snapshot): Option[Command] =
      current_command(snapshot)


    /* overlays */

    override def node_overlays(name: Document.Node.Name): Document.Node.Overlays =
      resources.node_overlays(name)

    override def insert_overlay(command: Command, fn: String, args: List[String]): Unit =
      resources.insert_overlay(command, fn, args)

    override def remove_overlay(command: Command, fn: String, args: List[String]): Unit =
      resources.remove_overlay(command, fn, args)


    /* hyperlinks */

    override def hyperlink_command(
      focus: Boolean, snapshot: Document.Snapshot, id: Document_ID.Generic,
      offset: Symbol.Offset = 0): Option[Hyperlink] =
    {
      if (snapshot.is_outdated) None
      else
        snapshot.find_command_position(id, offset).map(node_pos =>
          new Hyperlink {
            def follow(unit: Unit): Unit = channel.write(LSP.Caret_Update(node_pos, focus))
          })
    }


    /* dispatcher thread */

    override def assert_dispatcher[A](body: => A): A = session.assert_dispatcher(body)
    override def require_dispatcher[A](body: => A): A = session.require_dispatcher(body)
    override def send_dispatcher(body: => Unit): Unit = session.send_dispatcher(body)
    override def send_wait_dispatcher(body: => Unit): Unit = session.send_wait_dispatcher(body)
  }
}
