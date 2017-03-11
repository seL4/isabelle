/*  Title:      Tools/VSCode/src/server.scala
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


object Server
{
  /* Isabelle tool wrapper */

  private val default_text_length = "UTF-16"
  private lazy val default_logic = Isabelle_System.getenv("ISABELLE_LOGIC")

  val isabelle_tool = Isabelle_Tool("vscode_server", "VSCode Language Server for PIDE", args =>
  {
    try {
      var log_file: Option[Path] = None
      var text_length = Text.Length.encoding(default_text_length)
      var dirs: List[Path] = Nil
      var logic = default_logic
      var modes: List[String] = Nil
      var options = Options.init()
      var system_mode = false

      def text_length_choice: String =
        commas(Text.Length.encodings.map(
          { case (a, _) => if (a == default_text_length) a + " (default)" else a }))

      val getopts = Getopts("""
Usage: isabelle vscode_server [OPTIONS]

  Options are:
    -L FILE      enable logging on FILE
    -T LENGTH    text length encoding: """ + text_length_choice + """
    -d DIR       include session directory
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(default_logic) + """)
    -m MODE      add print mode for output
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -s           system build mode for session image

  Run the VSCode Language Server protocol (JSON RPC) over stdin/stdout.
""",
        "L:" -> (arg => log_file = Some(Path.explode(File.standard_path(arg)))),
        "T:" -> (arg => Text.Length.encoding(arg)),
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(File.standard_path(arg)))),
        "l:" -> (arg => logic = arg),
        "m:" -> (arg => modes = arg :: modes),
        "o:" -> (arg => options = options + arg),
        "s" -> (_ => system_mode = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val log = Logger.make(log_file)
      val channel = new Channel(System.in, System.out, log)
      val server = new Server(channel, options, text_length, logic, dirs, modes, system_mode, log)

      // prevent spurious garbage on the main protocol channel
      val orig_out = System.out
      try {
        System.setOut(new PrintStream(new OutputStream { def write(n: Int) {} }))
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

class Server(
  channel: Channel,
  options: Options,
  text_length: Text.Length = Text.Length.encoding(Server.default_text_length),
  session_name: String = Server.default_logic,
  session_dirs: List[Path] = Nil,
  modes: List[String] = Nil,
  system_mode: Boolean = false,
  log: Logger = No_Logger)
{
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


  /* input from client or file-system */

  private val delay_input: Standard_Thread.Delay =
    Standard_Thread.delay_last(options.seconds("vscode_input_delay"), channel.Error_Logger)
    { resources.flush_input(session) }

  private val delay_load: Standard_Thread.Delay =
    Standard_Thread.delay_last(options.seconds("vscode_load_delay"), channel.Error_Logger) {
      val (invoke_input, invoke_load) = resources.resolve_dependencies(session, file_watcher)
      if (invoke_input) delay_input.invoke()
      if (invoke_load) delay_load.invoke
    }

  private val file_watcher =
    File_Watcher(sync_documents(_), options.seconds("vscode_load_delay"))

  private def close_document(file: JFile)
  {
    if (resources.close_model(file)) {
      file_watcher.register_parent(file)
      sync_documents(Set(file))
      delay_input.invoke()
      delay_output.invoke()
    }
  }

  private def sync_documents(changed: Set[JFile])
  {
    resources.sync_models(changed)
    delay_input.invoke()
    delay_output.invoke()
  }

  private def change_document(file: JFile, changes: List[Protocol.TextDocumentChange])
  {
    changes.reverse.foreach(change =>
      resources.change_model(session, file, change.text, change.range))
    delay_input.invoke()
    delay_output.invoke()
  }



  /* output to client */

  private val delay_output: Standard_Thread.Delay =
    Standard_Thread.delay_last(options.seconds("vscode_output_delay"), channel.Error_Logger)
    {
      if (session.current_state().stable_tip_version.isEmpty) delay_output.invoke()
      else resources.flush_output(channel)
    }

  private val prover_output =
    Session.Consumer[Session.Commands_Changed](getClass.getName) {
      case changed =>
        resources.update_output(changed.nodes.toList.map(resources.node_file(_)))
        delay_output.invoke()
    }

  private val syslog =
    Session.Consumer[Prover.Message](getClass.getName) {
      case output: Prover.Output if output.is_syslog =>
        channel.log_writeln(resources.output_xml(output.message))
      case _ =>
    }


  /* init and exit */

  def init(id: Protocol.Id)
  {
    def reply(err: String)
    {
      channel.write(Protocol.Initialize.reply(id, err))
      if (err == "")
        channel.writeln("Welcome to Isabelle/" + session_name + " (" + Distribution.version + ")")
      else channel.error_message(err)
    }

    val try_session =
      try {
        if (!Build.build(options = options, build_heap = true, no_build = true,
              system_mode = system_mode, dirs = session_dirs, sessions = List(session_name)).ok)
        {
          val start_msg = "Build started for Isabelle/" + session_name + " ..."
          val fail_msg = "Session build failed -- prover process remains inactive!"

          val progress = channel.make_progress(verbose = true)
          progress.echo(start_msg); channel.writeln(start_msg)

          if (!Build.build(options = options, progress = progress, build_heap = true,
              system_mode = system_mode, dirs = session_dirs, sessions = List(session_name)).ok)
          {
            progress.echo(fail_msg); error(fail_msg)
          }
        }

        val base = Build.session_base(options, false, session_dirs, session_name)
        val resources =
          new VSCode_Resources(options, text_length, base, log)
          {
            override def commit(change: Session.Change): Unit =
              if (change.deps_changed || undefined_blobs(change.version.nodes).nonEmpty)
                delay_load.invoke()
          }

        Some(new Session(resources) {
          override def output_delay = options.seconds("editor_output_delay")
          override def prune_delay = options.seconds("editor_prune_delay")
          override def syslog_limit = options.int("editor_syslog_limit")
          override def reparse_limit = options.int("editor_reparse_limit")
        })
      }
      catch { case ERROR(msg) => reply(msg); None }

    for (session <- try_session) {
      var session_phase: Session.Consumer[Session.Phase] = null
      session_phase =
        Session.Consumer(getClass.getName) {
          case Session.Ready =>
            session.phase_changed -= session_phase
            session.update_options(options)
            reply("")
          case Session.Failed =>
            session.phase_changed -= session_phase
            reply("Prover startup failed")
          case _ =>
        }
      session.phase_changed += session_phase

      session.commands_changed += prover_output
      session.all_messages += syslog

      session.start(receiver =>
        Isabelle_Process(options = options, logic = session_name, dirs = session_dirs,
          modes = modes, receiver = receiver))

      session_.change(_ => Some(session))
    }
  }

  def shutdown(id: Protocol.Id)
  {
    def reply(err: String): Unit = channel.write(Protocol.Shutdown.reply(id, err))

    session_.change({
      case Some(session) =>
        var session_phase: Session.Consumer[Session.Phase] = null
        session_phase =
          Session.Consumer(getClass.getName) {
            case Session.Inactive =>
              session.phase_changed -= session_phase
              session.commands_changed -= prover_output
              session.all_messages -= syslog
              reply("")
            case _ =>
          }
        session.phase_changed += session_phase
        session.stop()
        delay_input.revoke()
        delay_output.revoke()
        file_watcher.shutdown()
        None
      case None =>
        reply("Prover inactive")
        None
    })
  }

  def exit() {
    log("\n")
    sys.exit(if (session_.value.isDefined) 1 else 0)
  }


  /* completion */

  def completion(id: Protocol.Id, node_pos: Line.Node_Position)
  {
    val result =
      (for ((rendering, offset) <- rendering_offset(node_pos))
        yield rendering.completion(Text.Range(offset - 1, offset))) getOrElse Nil
    channel.write(Protocol.Completion.reply(id, result))
  }


  /* hover */

  def hover(id: Protocol.Id, node_pos: Line.Node_Position)
  {
    val result =
      for {
        (rendering, offset) <- rendering_offset(node_pos)
        info <- rendering.tooltips(VSCode_Rendering.tooltip_elements, Text.Range(offset, offset + 1))
      } yield {
        val doc = rendering.model.content.doc
        val range = doc.range(info.range)
        val contents =
          info.info.map(t => Protocol.MarkedString(resources.output_pretty_tooltip(List(t))))
        (range, contents)
      }
    channel.write(Protocol.Hover.reply(id, result))
  }


  /* goto definition */

  def goto_definition(id: Protocol.Id, node_pos: Line.Node_Position)
  {
    val result =
      (for ((rendering, offset) <- rendering_offset(node_pos))
        yield rendering.hyperlinks(Text.Range(offset, offset + 1))) getOrElse Nil
    channel.write(Protocol.GotoDefinition.reply(id, result))
  }


  /* document highlights */

  def document_highlights(id: Protocol.Id, node_pos: Line.Node_Position)
  {
    val result =
      (for ((rendering, offset) <- rendering_offset(node_pos))
        yield {
          val doc = rendering.model.content.doc
          rendering.caret_focus_ranges(Text.Range(offset, offset + 1), doc.text_range)
            .map(r => Protocol.DocumentHighlight.text(doc.range(r)))
        }) getOrElse Nil
    channel.write(Protocol.DocumentHighlights.reply(id, result))
  }


  /* main loop */

  def start()
  {
    log("Server started " + Date.now())

    def handle(json: JSON.T)
    {
      try {
        json match {
          case Protocol.Initialize(id) => init(id)
          case Protocol.Shutdown(id) => shutdown(id)
          case Protocol.Exit(()) => exit()
          case Protocol.DidOpenTextDocument(file, _, _, text) =>
            change_document(file, List(Protocol.TextDocumentChange(None, text)))
          case Protocol.DidChangeTextDocument(file, _, changes) => change_document(file, changes)
          case Protocol.DidCloseTextDocument(file) => close_document(file)
          case Protocol.Completion(id, node_pos) => completion(id, node_pos)
          case Protocol.Hover(id, node_pos) => hover(id, node_pos)
          case Protocol.GotoDefinition(id, node_pos) => goto_definition(id, node_pos)
          case Protocol.DocumentHighlights(id, node_pos) => document_highlights(id, node_pos)
          case _ => log("### IGNORED")
        }
      }
      catch { case exn: Throwable => channel.log_error_message(Exn.message(exn)) }
    }

    @tailrec def loop()
    {
      channel.read() match {
        case Some(json) =>
          json match {
            case bulk: List[_] => bulk.foreach(handle(_))
            case _ => handle(json)
          }
          loop()
        case None => log("### TERMINATE")
      }
    }
    loop()
  }
}
