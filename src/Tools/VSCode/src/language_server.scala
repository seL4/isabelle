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


object Language_Server {
  type Editor = isabelle.Editor[Unit]


  /* Isabelle tool wrapper */

  private lazy val default_logic = Isabelle_System.getenv("ISABELLE_LOGIC")

  val isabelle_tool =
    Isabelle_Tool("vscode_server", "VSCode Language Server for PIDE", Scala_Project.here,
      { args =>
        try {
          var logic_ancestor: Option[String] = None
          var log_file: Option[Path] = None
          var logic_requirements = false
          var dirs: List[Path] = Nil
          var include_sessions: List[String] = Nil
          var logic = default_logic
          var modes: List[String] = Nil
          var no_build = false
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
    -n           no build of session image on startup
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
            "n" -> (_ => no_build = true),
            "o:" -> (arg => options = options + arg),
            "v" -> (_ => verbose = true))

          val more_args = getopts(args)
          if (more_args.nonEmpty) getopts.usage()

          val log = Logger.make_file(log_file)
          val channel = new Channel(System.in, System.out, log, verbose)
          val server =
            new Language_Server(channel, options, session_name = logic, session_dirs = dirs,
              include_sessions = include_sessions, session_ancestor = logic_ancestor,
              session_requirements = logic_requirements, session_no_build = no_build,
              modes = modes, log = log)

          // prevent spurious garbage on the main protocol channel
          val orig_out = System.out
          try {
            System.setOut(new PrintStream(OutputStream.nullOutputStream()))
            server.start()
          }
          finally { System.setOut(orig_out) }
        }
        catch {
          case exn: Throwable =>
            val channel = new Channel(System.in, System.out, new Logger)
            channel.error_message(Exn.message(exn))
            throw(exn)
        }
      })
}

class Language_Server(
  val channel: Channel,
  val options: Options,
  session_name: String = Language_Server.default_logic,
  include_sessions: List[String] = Nil,
  session_dirs: List[Path] = Nil,
  session_ancestor: Option[String] = None,
  session_requirements: Boolean = false,
  session_no_build: Boolean = false,
  modes: List[String] = Nil,
  log: Logger = new Logger
) {
  server =>


  /* prover session */

  private val session_ = Synchronized(None: Option[VSCode_Session])
  def session: VSCode_Session = session_.value getOrElse error("Server inactive")
  def resources: VSCode_Resources = session.resources
  def ml_settings: ML_Settings = session.store.ml_settings

  private val sledgehammer = VSCode_Sledgehammer(server)

  def rendering_offset(node_pos: Line.Node_Position): Option[(VSCode_Rendering, Text.Offset)] =
    for {
      rendering <- resources.get_rendering(new JFile(node_pos.name))
      offset <- rendering.model.content.doc.offset(node_pos.pos)
    } yield (rendering, offset)

  private val dynamic_output = Dynamic_Output(server)


  /* input from client or file-system */

  private val file_watcher: File_Watcher =
    File_Watcher(sync_documents, options.seconds("vscode_load_delay"))

  private val delay_input: Delay =
    Delay.last(options.seconds("vscode_input_delay"), channel.Error_Logger) {
      resources.flush_input(session, channel)
    }

  private val delay_load: Delay =
    Delay.last(options.seconds("vscode_load_delay"), channel.Error_Logger) {
      val (invoke_input, invoke_load) =
        resources.resolve_dependencies(session, editor, file_watcher)
      if (invoke_input) delay_input.invoke()
      if (invoke_load) delay_load.invoke()
    }

  private def close_document(file: JFile): Unit = {
    if (resources.close_model(file)) {
      file_watcher.register_parent(file)
      sync_documents(Set(file))
      delay_input.invoke()
      delay_output.invoke()
    }
  }

  private def sync_documents(changed: Set[JFile]): Unit = {
    resources.sync_models(changed)
    delay_input.invoke()
    delay_output.invoke()
  }

  private def change_document(
    file: JFile,
    version: Long,
    changes: List[LSP.TextDocumentChange]
  ): Unit = {
    changes.foreach(change =>
      resources.change_model(session, editor, file, version, change.text, change.range))

    delay_input.invoke()
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
    delay_input.invoke()
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
        val session_background =
          Sessions.background(
            options, session_name, dirs = session_dirs,
            include_sessions = include_sessions, session_ancestor = session_ancestor,
            session_requirements = session_requirements).check_errors

        def build(no_build: Boolean = false): Build.Results =
          Build.build(options,
            selection = Sessions.Selection.session(session_background.session_name),
            build_heap = true, no_build = no_build, dirs = session_dirs,
            infos = session_background.infos)

        if (!session_no_build && !build(no_build = true).ok) {
          val start_msg = "Build started for Isabelle/" + session_background.session_name + " ..."
          val fail_msg = "Session build failed -- prover process remains inactive!"

          val progress = channel.progress(verbose = true)
          progress.echo(start_msg); channel.writeln(start_msg)

          if (!build().ok) { progress.echo(fail_msg); error(fail_msg) }
        }

        val session_resources = new VSCode_Resources(options, session_background, log)
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
        delay_input.revoke()
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
        yield rendering.hyperlinks(Text.Range(offset, offset + 1))) getOrElse Nil
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
    def extract_sendbacks(body: XML.Body): List[(String, Properties.T)] = {
      body match {
        case XML.Elem(Markup(Markup.SENDBACK, p), b) :: rest =>
          (XML.content(b), p) :: extract_sendbacks(rest)
        case XML.Elem(m, b) :: rest => extract_sendbacks(b ++ rest)
        case e :: rest => extract_sendbacks(rest)
        case Nil => Nil
      }
    }

    for {
      model <- resources.get_model(file)
      version <- model.version
      snapshot = resources.snapshot(model)
      doc = model.content.doc
      text_range <- doc.text_range(range)
      text_range2 = Text.Range(text_range.start - 1, text_range.stop + 1)
    } {
      val edits = snapshot
        .select(
          text_range2,
          Markup.Elements.full,
          command_states => _ => Some(command_states.flatMap(_.results.iterator.map(_._2).toList)))
        .flatMap(info => extract_sendbacks(info.info).flatMap {
          (s, p) =>
            for {
              id <- Position.Id.unapply(p)
              (node, command) <- snapshot.find_command(id)
              start <- node.command_start(command)
              range = command.core_range + start
              current_text <- model.get_text(range)
              line_range = doc.range(range)

              whole_line = doc.lines(line_range.start.line)
              indent = whole_line.text.takeWhile(_.isWhitespace)
              padding = p.contains(Markup.PADDING_COMMAND)

              indented_text = Library.prefix_lines(indent, s)
              edit_text =
                resources.output_edit(
                  if (padding) current_text + "\n" + indented_text else current_text + s)
              edit = LSP.TextEdit(line_range, edit_text)
            } yield (s, edit) 
        })
        .distinct

      val actions = edits.map((name, edit) => {
        val text_edits = List(LSP.TextDocumentEdit(file, Some(version), List(edit)))

        LSP.CodeAction(name, text_edits)
      })
      val reply = LSP.CodeActionRequest.reply(id, actions)

      channel.write(reply)
    }
  }


  /* symbols */

  def symbols_request(id: LSP.Id): Unit = {
    val symbols = Component_VSCodium.symbols
    channel.write(LSP.Symbols_Request.reply(id, symbols))
  }
  
  def symbols_convert_request(id: LSP.Id, text: String, unicode: Boolean): Unit = {
    val converted = Symbol.output(unicode, text)
    channel.write(LSP.Symbols_Convert_Request.reply(id, converted))
  }

  def symbols_panel_request(): Unit = {
    val abbrevs =
      resources.get_caret().flatMap { caret =>
        resources.get_model(caret.file).map(_.syntax().abbrevs)
      }.getOrElse(session.resources.session_base.overall_syntax.abbrevs)

    channel.write(LSP.Symbols_Response(Symbol.symbols, abbrevs))
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
          case LSP.Symbols_Request(id) => symbols_request(id)
          case LSP.Symbols_Convert_Request(id, text, boolean) =>
            symbols_convert_request(id, text, boolean)
          case LSP.Preview_Request(file, column) => preview_request(file, column)
          case LSP.Symbols_Panel_Request => symbols_panel_request()
          case LSP.Documentation_Request => documentation_request()
          case LSP.Sledgehammer_Request(provers, isar, try0) =>
            sledgehammer.handle_request(provers, isar, try0)
          case LSP.Sledgehammer_Cancel() => sledgehammer.cancel()
          case LSP.Sledgehammer_Locate() => sledgehammer.locate()
          case LSP.Sledgehammer_Insert() => sledgehammer.insert()
          case LSP.Sledgehammer_Provers_Request() => sledgehammer.send_provers()
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


  /* abstract editor operations */

  object editor extends Language_Server.Editor {
    /* PIDE session and document model */

    override def session: VSCode_Session = server.session
    override def flush(): Unit = resources.flush_input(session, channel)
    override def invoke(): Unit = delay_input.invoke()

    override def get_models(): Iterable[Document.Model] = resources.get_models()


    /* current situation */

    override def current_node(context: Unit): Option[Document.Node.Name] =
      resources.get_caret().map(_.model.node_name)
    override def current_node_snapshot(context: Unit): Option[Document.Snapshot] =
      resources.get_caret().map(caret => resources.snapshot(caret.model))

    override def node_snapshot(name: Document.Node.Name): Document.Snapshot = {
      resources.get_snapshot(name) match {
        case Some(snapshot) => snapshot
        case None => session.snapshot(name)
      }
    }

    def current_command(snapshot: Document.Snapshot): Option[Command] = {
      resources.get_caret() match {
        case Some(caret) if snapshot.loaded_theory_command(caret.offset).isEmpty =>
          snapshot.current_command(caret.node_name, caret.offset)
        case _ => None
      }
    }
    override def current_command(context: Unit, snapshot: Document.Snapshot): Option[Command] =
      current_command(snapshot)


    /* output messages */

    override def output_state(): Boolean = resources.options.bool("editor_output_state")


    /* overlays */

    override def node_overlays(name: Document.Node.Name): Document.Node.Overlays =
      resources.node_overlays(name)

    override def insert_overlay(command: Command, fn: String, args: List[String]): Unit =
      resources.insert_overlay(command, fn, args)

    override def remove_overlay(command: Command, fn: String, args: List[String]): Unit =
      resources.remove_overlay(command, fn, args)


    /* hyperlinks */

    override def hyperlink_command(
      focus: Boolean,
      snapshot: Document.Snapshot,
      id: Document_ID.Generic,
      offset: Symbol.Offset = 0
    ): Option[Hyperlink] = {
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
