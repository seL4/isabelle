/*  Title:      Tools/VSCode/src/language_server.scala
    Author:     Makarius

Server for VS Code Language Server Protocol 2.0/3.0, see also
https://github.com/Microsoft/language-server-protocol
https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md

PIDE protocol extensions depend on system option "vscode_pide_extensions".
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}

import scala.collection.mutable
import scala.annotation.tailrec


object Language_Server {
  /* build session */

  def build_session(options: Options, logic: String,
    build_progress: Progress = new Progress,
    session_dirs: List[Path] = Nil,
    include_sessions: List[String] = Nil,
    session_ancestor: Option[String] = None,
    session_requirements: Boolean = false,
    session_no_build: Boolean = false,
    build_started: String => Unit = _ => (),
    build_failed: String => Unit = _ => ()
  ): Sessions.Background = {
    val session_background =
      Sessions.background(
        options, logic, dirs = session_dirs,
        include_sessions = include_sessions, session_ancestor = session_ancestor,
        session_requirements = session_requirements).check_errors

    def build(no_build: Boolean = false, progress: Progress = new Progress): Build.Results =
      Build.build(options,
        selection = Sessions.Selection.session(logic),
        build_heap = true, no_build = no_build, dirs = session_dirs,
        infos = session_background.infos,
        progress = progress)

    if (!session_no_build && !build(no_build = true).ok) {
      build_started(logic)
      if (!build(progress = build_progress).ok) build_failed(logic)
    }

    session_background
  }


  /* abstract editor operations */

  class Editor(server: Language_Server) extends isabelle.Editor {
    type Context = Unit
    type Session = VSCode_Session


    /* PIDE session and document model */

    override def session: VSCode_Session = server.session
    override def flush(): Unit = session.resources.flush_input(session, server.channel)

    override def get_models(): Iterable[Document.Model] = session.resources.get_models()


    /* input from client */

    private val delay_input: Delay =
      Delay.last(server.options.seconds("vscode_input_delay"), server.channel.Error_Logger) {
        session.resources.flush_input(session, server.channel)
      }

    override def invoke(): Unit = delay_input.invoke()
    override def revoke(): Unit = delay_input.revoke()


    /* current situation */

    override def current_node(context: Unit): Option[Document.Node.Name] =
      session.resources.get_caret().map(_.model.node_name)
    override def current_node_snapshot(context: Unit): Option[Document.Snapshot] =
      session.resources.get_caret().map(caret => session.resources.snapshot(caret.model))

    override def node_snapshot(name: Document.Node.Name): Document.Snapshot = {
      session.resources.get_snapshot(name) match {
        case Some(snapshot) => snapshot
        case None => session.snapshot(name)
      }
    }

    def current_command(snapshot: Document.Snapshot): Option[Command] = {
      session.resources.get_caret() match {
        case Some(caret) if snapshot.loaded_theory_command(caret.offset).isEmpty =>
          snapshot.current_command(caret.node_name, caret.offset)
        case _ => None
      }
    }
    override def current_command(context: Unit, snapshot: Document.Snapshot): Option[Command] =
      current_command(snapshot)


    /* output messages */

    override def output_state(): Boolean =
      session.resources.options.bool("editor_output_state")


    /* overlays */

    override def node_overlays(name: Document.Node.Name): Document.Node.Overlays =
      session.resources.node_overlays(name)

    override def insert_overlay(command: Command, fn: String, args: List[String]): Unit =
      session.resources.insert_overlay(command, fn, args)

    override def remove_overlay(command: Command, fn: String, args: List[String]): Unit =
      session.resources.remove_overlay(command, fn, args)


    /* hyperlinks */

    override def hyperlink_command(
      snapshot: Document.Snapshot,
      id: Document_ID.Generic,
      offset: Symbol.Offset = 0,
      focus: Boolean = false,
    ): Option[Hyperlink] = {
      if (snapshot.is_outdated) None
      else
        snapshot.find_command_position(id, offset).map(node_pos =>
          new Hyperlink {
            def follow(unit: Unit): Unit = server.channel.write(LSP.Caret_Update(node_pos, focus))
          })
    }


    /* dispatcher thread */

    override def assert_dispatcher[A](body: => A): A = session.assert_dispatcher(body)
    override def require_dispatcher[A](body: => A): A = session.require_dispatcher(body)
    override def send_dispatcher(body: => Unit): Unit = session.send_dispatcher(body)
    override def send_wait_dispatcher(body: => Unit): Unit = session.send_wait_dispatcher(body)
  }
}

class Language_Server(
  val channel: Channel,
  val options: Options,
  session_name: String = Isabelle_System.default_logic(),
  include_sessions: List[String] = Nil,
  session_dirs: List[Path] = Nil,
  session_ancestor: Option[String] = None,
  session_requirements: Boolean = false,
  session_no_build: Boolean = false,
  modes: List[String] = Nil,
  log: Logger = new Logger
) {
  server =>

  val editor: Language_Server.Editor = new Language_Server.Editor(server)


  /* prover session */

  private val session_ = Synchronized(None: Option[VSCode_Session])
  def session: VSCode_Session = session_.value getOrElse error("Server inactive")
  def resources: VSCode_Resources = session.resources
  def ml_settings: ML_Settings = session.store.ml_settings

  private val sledgehammer = new VSCode_Sledgehammer(server)

  def rendering_offset(node_pos: Line.Node_Position): Option[(VSCode_Rendering, Text.Offset)] =
    for {
      rendering <- resources.get_rendering(new JFile(node_pos.name))
      offset <- rendering.model.content.doc.offset(node_pos.pos)
    } yield (rendering, offset)

  private val dynamic_output = Dynamic_Output(server)


  /* input from client or file-system */

  private val file_watcher: File_Watcher =
    File_Watcher(sync_documents, options.seconds("vscode_load_delay"))

  private val delay_load: Delay =
    Delay.last(options.seconds("vscode_load_delay"), channel.Error_Logger) {
      val (invoke_input, invoke_load) =
        resources.resolve_dependencies(session, editor, file_watcher)
      if (invoke_input) editor.invoke()
      if (invoke_load) delay_load.invoke()
    }

  private def close_document(file: JFile): Unit = {
    if (resources.close_model(file)) {
      file_watcher.register_parent(file)
      sync_documents(Set(file))
      editor.invoke()
      delay_output.invoke()
    }
  }

  private def sync_documents(changed: Set[JFile]): Unit = {
    resources.sync_models(changed)
    editor.invoke()
    delay_output.invoke()
  }

  private def change_document(
    file: JFile,
    version: Long,
    changes: List[LSP.TextDocumentChange]
  ): Unit = {
    changes.foreach(change =>
      resources.change_model(session, editor, file, version, change.text, change.range))

    editor.invoke()
    delay_output.invoke()
  }


  /* caret handling */

  private val delay_caret_update: Delay =
    Delay.last(options.seconds("vscode_input_delay"), channel.Error_Logger) {
      session.caret_focus.post(Session.Caret_Focus)
    }

  private def update_caret(caret: Option[(JFile, Line.Position)]): Unit = {
    resources.update_caret(caret)
    delay_caret_update.invoke()
    editor.invoke()
  }


  /* preview */

  private lazy val preview_panel = new Preview_Panel(resources)

  private lazy val delay_preview: Delay =
    Delay.last(options.seconds("vscode_output_delay"), channel.Error_Logger) {
      if (preview_panel.flush(channel)) delay_preview.invoke()
    }

  private def preview_request(file: JFile, column: Int): Unit = {
    preview_panel.request(file, column)
    delay_preview.invoke()
  }


  /* output to client */

  private val delay_output: Delay =
    Delay.last(options.seconds("vscode_output_delay"), channel.Error_Logger) {
      if (resources.flush_output(channel)) delay_output.invoke()
    }

  def update_output(changed_nodes: Iterable[JFile]): Unit = {
    resources.update_output(changed_nodes)
    delay_output.invoke()
  }

  def update_output_visible(): Unit = {
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
      case output => channel.log_writeln(resources.output_text(XML.content(output.message)))
    }


  /* decoration request */

  private def decoration_request(file: JFile): Unit =
    resources.force_decorations(channel, file)


  /* init and exit */

  def init(id: LSP.Id): Unit = {
    def reply_ok(msg: String): Unit = {
      channel.write(LSP.Initialize.reply(id, ""))
      channel.writeln(msg)
    }

    def reply_error(msg: String): Unit = {
      channel.write(LSP.Initialize.reply(id, msg))
      channel.error_message(msg)
    }

    val try_session =
      try {
        val progress = channel.progress(verbose = true)
        val session_background =
          Language_Server.build_session(options, session_name,
            session_dirs = session_dirs,
            include_sessions = include_sessions,
            session_ancestor = session_ancestor,
            session_requirements = session_requirements,
            session_no_build = session_no_build,
            build_started = { logic =>
              val msg = Build.build_logic_started(logic)
              progress.echo(msg)
              channel.writeln(msg) },
            build_failed = { logic =>
              val msg = Build.build_logic_failed(logic, editor = true)
              progress.echo(msg)
              error(msg) })

        val session_resources = new VSCode_Resources(options, session_background, log = log)
        val session_options = options.bool.update("editor_output_state", true)
        val session =
          new VSCode_Session(session_options, session_resources) {
            override def deps_changed(): Unit = delay_load.invoke()
          }

        Some((session_background, session))
      }
      catch { case ERROR(msg) => reply_error(msg); None }

    for ((session_background, session) <- try_session) {
      val store = Store(options)
      val session_heaps =
        store.session_heaps(session_background, logic = session_background.session_name)

      session_.change(_ => Some(session))

      session.commands_changed += prover_output
      session.syslog_messages += syslog_messages

      dynamic_output.init()
      sledgehammer.init()

      try {
        Isabelle_Process.start(
          options, session, session_background, session_heaps, modes = modes).await_startup()
        reply_ok(
          "Welcome to Isabelle/" + session_background.session_name +
          Isabelle_System.isabelle_heading())
      }
      catch { case ERROR(msg) => reply_error(msg) }
    }
  }

  def shutdown(id: LSP.Id): Unit = {
    def reply(err: String): Unit = channel.write(LSP.Shutdown.reply(id, err))

    session_.change({
      case Some(session) =>
        session.commands_changed -= prover_output
        session.syslog_messages -= syslog_messages

        dynamic_output.exit()

        delay_load.revoke()
        file_watcher.shutdown()
        editor.revoke()
        delay_output.revoke()
        delay_caret_update.revoke()
        delay_preview.revoke()
        sledgehammer.exit()

        val result = session.stop()
        if (result.ok) reply("")
        else reply("Prover shutdown failed: " + result.rc)
        None
      case None =>
        reply("Prover inactive")
        None
    })
  }

  def exit(): Unit = {
    log("\n")
    sys.exit(if (session_.value.isEmpty) Process_Result.RC.ok else Process_Result.RC.failure)
  }


  /* completion */

  def completion(id: LSP.Id, node_pos: Line.Node_Position): Unit = {
    val result =
      (for ((rendering, offset) <- rendering_offset(node_pos))
        yield rendering.completion(node_pos, offset)) getOrElse Nil
    channel.write(LSP.Completion.reply(id, result))
  }


  /* spell-checker dictionary */

  def update_dictionary(include: Boolean, permanent: Boolean): Unit = {
    for {
      spell_checker <- resources.spell_checker.get
      caret <- resources.get_caret()
      rendering = resources.rendering(caret.model)
      range = rendering.before_caret_range(caret.offset)
      Text.Info(_, word) <- Spell_Checker.current_word(rendering, range)
    } {
      spell_checker.update(word, include, permanent)
      update_output_visible()
    }
  }

  def reset_dictionary(): Unit = {
    for (spell_checker <- resources.spell_checker.get) {
      spell_checker.reset()
      update_output_visible()
    }
  }


  /* hover */

  def hover(id: LSP.Id, node_pos: Line.Node_Position): Unit = {
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

  def goto_definition(id: LSP.Id, node_pos: Line.Node_Position): Unit = {
    val result =
      (for ((rendering, offset) <- rendering_offset(node_pos))
        yield rendering.hyperlinks(Text.Range(offset, offset + 1)).toList.map(_.info)) getOrElse Nil
    channel.write(LSP.GotoDefinition.reply(id, result))
  }


  /* document highlights */

  def document_highlights(id: LSP.Id, node_pos: Line.Node_Position): Unit = {
    val result =
      (for ((rendering, offset) <- rendering_offset(node_pos))
        yield {
          val model = rendering.model
          rendering.caret_focus_ranges(Text.Range(offset, offset + 1), model.content.text_range)
            .map(r => LSP.DocumentHighlight.text(model.content.doc.range(r)))
        }) getOrElse Nil
    channel.write(LSP.DocumentHighlights.reply(id, result))
  }


  /* code actions */

  def code_action_request(id: LSP.Id, file: JFile, range: Line.Range): Unit = {
    for {
      model <- resources.get_model(file)
      version <- model.version
      doc = model.content.doc
      text_range <- doc.text_range(range)
    } {
      val snapshot = resources.snapshot(model)
      val results =
        snapshot.command_results(Text.Range(text_range.start - 1, text_range.stop + 1))
          .iterator.map(_._2).toList
      val actions =
        List.from(
          for {
            (snippet, props) <- Protocol.sendback_snippets(results).iterator
            id <- Position.Id.unapply(props)
            command <- snapshot.get_command(id)
            start <- snapshot.command_start(command)
            range = command.core_range + start
            current_text <- model.get_text(range)
          } yield {
            val line_range = doc.range(range)
            val edit_text =
              if (props.contains(Markup.PADDING_COMMAND)) {
                val whole_line = doc.lines(line_range.start.line)
                val indent = whole_line.text.takeWhile(_.isWhitespace)
                current_text + "\n" + Library.prefix_lines(indent, snippet)
              }
              else current_text + snippet
            val edit = LSP.TextEdit(line_range, resources.output_edit(edit_text))
            LSP.CodeAction(snippet, List(LSP.TextDocumentEdit(file, Some(version), List(edit))))
          })
      channel.write(LSP.CodeActionRequest.reply(id, actions))
    }
  }


  /* abbrevs */

  def abbrevs_request(): Unit = {
    val syntax = session.resources.session_base.overall_syntax
    channel.write(LSP.Abbrevs_Request.reply(syntax.abbrevs))
  }


  def documentation_request(): Unit =
    channel.write(LSP.Documentation_Response(ml_settings))


  /* main loop */

  def start(): Unit = {
    log("Server started " + Date.now())

    def handle(json: JSON.T): Unit = {
      try {
        json match {
          case LSP.Initialize(id) => init(id)
          case LSP.Initialized() =>
          case LSP.Shutdown(id) => shutdown(id)
          case LSP.Exit() => exit()
          case LSP.DidOpenTextDocument(file, _, version, text) =>
            change_document(file, version, List(LSP.TextDocumentChange(None, text)))
            delay_load.invoke()
          case LSP.DidChangeTextDocument(file, version, changes) =>
            change_document(file, version, changes)
          case LSP.DidCloseTextDocument(file) => close_document(file)
          case LSP.Completion(id, node_pos) => completion(id, node_pos)
          case LSP.Include_Word() => update_dictionary(true, false)
          case LSP.Include_Word_Permanently() => update_dictionary(true, true)
          case LSP.Exclude_Word() => update_dictionary(false, false)
          case LSP.Exclude_Word_Permanently() => update_dictionary(false, true)
          case LSP.Reset_Words() => reset_dictionary()
          case LSP.Hover(id, node_pos) => hover(id, node_pos)
          case LSP.GotoDefinition(id, node_pos) => goto_definition(id, node_pos)
          case LSP.DocumentHighlights(id, node_pos) => document_highlights(id, node_pos)
          case LSP.CodeActionRequest(id, file, range) => code_action_request(id, file, range)
          case LSP.Decoration_Request(file) => decoration_request(file)
          case LSP.Caret_Update(caret) => update_caret(caret)
          case LSP.Output_Set_Margin(margin) => dynamic_output.set_margin(margin)
          case LSP.State_Init(id) => State_Panel.init(id, server)
          case LSP.State_Exit(state_id) => State_Panel.exit(state_id)
          case LSP.State_Locate(state_id) => State_Panel.locate(state_id)
          case LSP.State_Update(state_id) => State_Panel.update(state_id)
          case LSP.State_Auto_Update(state_id, enabled) =>
            State_Panel.auto_update(state_id, enabled)
          case LSP.State_Set_Margin(state_id, margin) => State_Panel.set_margin(state_id, margin)
          case LSP.Preview_Request(file, column) => preview_request(file, column)
          case LSP.Abbrevs_Request() => abbrevs_request()
          case LSP.Documentation_Request() => documentation_request()
          case LSP.Sledgehammer_Provers_Request() => sledgehammer.provers()
          case LSP.Sledgehammer_Request(args) => sledgehammer.request(args)
          case LSP.Sledgehammer_Cancel() => sledgehammer.cancel()
          case LSP.Sledgehammer_Locate() => sledgehammer.locate()
          case LSP.Sledgehammer_Sendback(text) => sledgehammer.sendback(text)
          case _ => if (!LSP.ResponseMessage.is_empty(json)) log("### IGNORED")
        }
      }
      catch { case exn: Throwable => channel.log_error_message(Exn.message(exn)) }
    }

    @tailrec def loop(): Unit = {
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
}
