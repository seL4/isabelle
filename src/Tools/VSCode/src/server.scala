/*  Title:      Tools/VSCode/src/server.scala
    Author:     Makarius

Server for VS Code Language Server Protocol 2.0, see also
https://github.com/Microsoft/language-server-protocol
https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md
*/

package isabelle.vscode


import isabelle._

import java.io.{PrintStream, OutputStream}

import scala.annotation.tailrec


object Server
{
  /* Isabelle tool wrapper */

  private lazy val default_logic = Isabelle_System.getenv("ISABELLE_LOGIC")

  val isabelle_tool = Isabelle_Tool("vscode_server", "VSCode Language Server for PIDE", args =>
  {
    var log_file: Option[Path] = None
    var dirs: List[Path] = Nil
    var logic = default_logic
    var modes: List[String] = Nil
    var options = Options.init()

    val getopts = Getopts("""
Usage: isabelle vscode_server [OPTIONS]

  Options are:
    -L FILE      enable logging on FILE
    -d DIR       include session directory
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(logic) + """)
    -m MODE      add print mode for output
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Run the VSCode Language Server protocol (JSON RPC) over stdin/stdout.
""",
      "L:" -> (arg => log_file = Some(Path.explode(arg))),
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "l:" -> (arg => logic = arg),
      "m:" -> (arg => modes = arg :: modes),
      "o:" -> (arg => options = options + arg))

    val more_args = getopts(args)
    if (more_args.nonEmpty) getopts.usage()

    if (!Build.build(options = options, build_heap = true, no_build = true,
          dirs = dirs, sessions = List(logic)).ok)
      error("Missing logic image " + quote(logic))

    val channel = new Channel(System.in, System.out, log_file)
    val server = new Server(channel, options, logic, dirs, modes)

    // prevent spurious garbage on the main protocol channel
    val orig_out = System.out
    try {
      System.setOut(new PrintStream(new OutputStream { def write(n: Int) {} }))
      server.start()
    }
    finally { System.setOut(orig_out) }
  })


  /* server state */

  sealed case class State(
    session: Option[Session] = None,
    models: Map[String, Document_Model] = Map.empty)
}

class Server(
  channel: Channel,
  options: Options,
  session_name: String = Server.default_logic,
  session_dirs: List[Path] = Nil,
  modes: List[String] = Nil)
{
  /* server state */

  private val state = Synchronized(Server.State())

  def session: Session = state.value.session getOrElse error("Session inactive")
  def resources: URI_Resources = session.resources.asInstanceOf[URI_Resources]


  /* init and exit */

  def initialize(reply: String => Unit)
  {
    val content = Build.session_content(options, false, session_dirs, session_name)
    val resources =
      new URI_Resources(content.loaded_theories, content.known_theories, content.syntax)

    val session =
      new Session(resources) {
        override def output_delay = options.seconds("editor_output_delay")
        override def prune_delay = options.seconds("editor_prune_delay")
        override def syslog_limit = options.int("editor_syslog_limit")
        override def reparse_limit = options.int("editor_reparse_limit")
      }

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

    session.start(receiver =>
      Isabelle_Process(options = options, logic = session_name, dirs = session_dirs,
        modes = modes, receiver = receiver))

    state.change(_.copy(session = Some(session)))
  }

  def shutdown(reply: String => Unit)
  {
    state.change(st =>
      st.session match {
        case None => reply("Prover inactive"); st
        case Some(session) =>
          var session_phase: Session.Consumer[Session.Phase] = null
          session_phase =
            Session.Consumer(getClass.getName) {
              case Session.Inactive =>
                session.phase_changed -= session_phase
                reply("")
              case _ =>
            }
          session.phase_changed += session_phase
          session.stop()
          st.copy(session = None)
      })
  }

  def exit() { sys.exit(if (state.value.session.isDefined) 1 else 0) }


  /* document management */

  private val delay_flush =
    Standard_Thread.delay_last(options.seconds("editor_input_delay")) {
      state.change(st =>
        {
          val models = st.models
          val changed = (for { entry <- models.iterator if entry._2.changed } yield entry).toList
          val edits = for { (_, model) <- changed; edit <- model.node_edits } yield edit
          val models1 =
            (models /: changed)({ case (m, (uri, model)) => m + (uri -> model.unchanged) })

          session.update(Document.Blobs.empty, edits)
          st.copy(models = models1)
        })
    }

  def update_document(uri: String, text: String)
  {
    state.change(st =>
      {
        val node_name = resources.node_name(uri)
        val model = Document_Model(session, Line.Document(text), node_name)
        st.copy(models = st.models + (uri -> model))
      })
    delay_flush.invoke()
  }


  /* tooltips -- see $ISABELLE_HOME/src/Tools/jEdit/rendering.scala */

  def hover(uri: String, pos: Line.Position): Option[(Line.Range, List[String])] =
    for {
      model <- state.value.models.get(uri)
      snapshot = model.snapshot()
      offset <- model.doc.offset(pos)
      info <- tooltip(snapshot, Text.Range(offset, offset + 1))
    } yield {
      val r = Line.Range(model.doc.position(info.range.start), model.doc.position(info.range.stop))
      val s = Pretty.string_of(info.info, margin = tooltip_margin.toDouble)
      (r, List("```\n" + s + "\n```"))
    }

  private val tooltip_descriptions =
    Map(
      Markup.CITATION -> "citation",
      Markup.TOKEN_RANGE -> "inner syntax token",
      Markup.FREE -> "free variable",
      Markup.SKOLEM -> "skolem variable",
      Markup.BOUND -> "bound variable",
      Markup.VAR -> "schematic variable",
      Markup.TFREE -> "free type variable",
      Markup.TVAR -> "schematic type variable")

  private val tooltip_elements =
    Markup.Elements(Markup.LANGUAGE, Markup.EXPRESSION, Markup.TIMING, Markup.ENTITY,
      Markup.SORTING, Markup.TYPING, Markup.CLASS_PARAMETER, Markup.ML_TYPING,
      Markup.ML_BREAKPOINT, Markup.PATH, Markup.DOC, Markup.URL, Markup.MARKDOWN_PARAGRAPH,
      Markup.Markdown_List.name) ++ Markup.Elements(tooltip_descriptions.keySet)

  private def pretty_typing(kind: String, body: XML.Body): XML.Tree =
    Pretty.block(XML.Text(kind) :: Pretty.brk(1) :: body)

  private def timing_threshold: Double = options.real("jedit_timing_threshold")

  def tooltip(snapshot: Document.Snapshot, range: Text.Range): Option[Text.Info[XML.Body]] =
  {
    def add(prev: Text.Info[(Timing, Vector[(Boolean, XML.Tree)])],
      r0: Text.Range, p: (Boolean, XML.Tree)): Text.Info[(Timing, Vector[(Boolean, XML.Tree)])] =
    {
      val r = snapshot.convert(r0)
      val (t, info) = prev.info
      if (prev.range == r)
        Text.Info(r, (t, info :+ p))
      else Text.Info(r, (t, Vector(p)))
    }

    val results =
      snapshot.cumulate[Text.Info[(Timing, Vector[(Boolean, XML.Tree)])]](
        range, Text.Info(range, (Timing.zero, Vector.empty)), tooltip_elements, _ =>
        {
          case (Text.Info(r, (t1, info)), Text.Info(_, XML.Elem(Markup.Timing(t2), _))) =>
            Some(Text.Info(r, (t1 + t2, info)))

          case (prev, Text.Info(r, XML.Elem(Markup.Entity(kind, name), _)))
          if kind != "" &&
            kind != Markup.ML_DEF &&
            kind != Markup.ML_OPEN &&
            kind != Markup.ML_STRUCTURE =>
            val kind1 = Word.implode(Word.explode('_', kind))
            val txt1 =
              if (name == "") kind1
              else if (kind1 == "") quote(name)
              else kind1 + " " + quote(name)
            val t = prev.info._1
            val txt2 =
              if (kind == Markup.COMMAND && t.elapsed.seconds >= timing_threshold)
                "\n" + t.message
              else ""
            Some(add(prev, r, (true, XML.Text(txt1 + txt2))))

          case (prev, Text.Info(r, XML.Elem(Markup.Doc(name), _))) =>
            val text = "doc " + quote(name)
            Some(add(prev, r, (true, XML.Text(text))))

          case (prev, Text.Info(r, XML.Elem(Markup.Url(name), _))) =>
            Some(add(prev, r, (true, XML.Text("URL " + quote(name)))))

          case (prev, Text.Info(r, XML.Elem(Markup(name, _), body)))
          if name == Markup.SORTING || name == Markup.TYPING =>
            Some(add(prev, r, (true, pretty_typing("::", body))))

          case (prev, Text.Info(r, XML.Elem(Markup(Markup.CLASS_PARAMETER, _), body))) =>
            Some(add(prev, r, (true, Pretty.block(0, body))))

          case (prev, Text.Info(r, XML.Elem(Markup(Markup.ML_TYPING, _), body))) =>
            Some(add(prev, r, (false, pretty_typing("ML:", body))))

          case (prev, Text.Info(r, XML.Elem(Markup.Language(language, _, _, _), _))) =>
            val lang = Word.implode(Word.explode('_', language))
            Some(add(prev, r, (true, XML.Text("language: " + lang))))

          case (prev, Text.Info(r, XML.Elem(Markup.Expression(kind), _))) =>
            val descr = if (kind == "") "expression" else "expression: " + kind
            Some(add(prev, r, (true, XML.Text(descr))))

          case (prev, Text.Info(r, XML.Elem(Markup(Markup.MARKDOWN_PARAGRAPH, _), _))) =>
            Some(add(prev, r, (true, XML.Text("Markdown: paragraph"))))
          case (prev, Text.Info(r, XML.Elem(Markup.Markdown_List(kind), _))) =>
            Some(add(prev, r, (true, XML.Text("Markdown: " + kind))))

          case (prev, Text.Info(r, XML.Elem(Markup(name, _), _))) =>
            tooltip_descriptions.get(name).
              map(descr => add(prev, r, (true, XML.Text(descr))))
        }).map(_.info)

    results.map(_.info).flatMap(res => res._2.toList) match {
      case Nil => None
      case tips =>
        val r = Text.Range(results.head.range.start, results.last.range.stop)
        val all_tips = (tips.filter(_._1) ++ tips.filter(!_._1).lastOption.toList).map(_._2)
        Some(Text.Info(r, Library.separate(Pretty.fbrk, all_tips)))
    }
  }

  def tooltip_margin: Int = options.int("jedit_tooltip_margin")


  /* main loop */

  def start()
  {
    channel.log("\nServer started " + Date.now())

    def handle(json: JSON.T)
    {
      try {
        json match {
          case Protocol.Initialize(id) =>
            def initialize_reply(err: String)
            {
              channel.write(Protocol.Initialize.reply(id, err))
              if (err == "") {
                channel.write(Protocol.DisplayMessage(Protocol.MessageType.Info,
                  "Welcome to Isabelle/" + session_name + " (" + Distribution.version + ")"))
              }
              else channel.write(Protocol.DisplayMessage(Protocol.MessageType.Error, err))
            }
            initialize(initialize_reply _)
          case Protocol.Shutdown(id) =>
            shutdown((error: String) => channel.write(Protocol.Shutdown.reply(id, error)))
          case Protocol.Exit =>
            exit()
          case Protocol.DidOpenTextDocument(uri, lang, version, text) =>
            update_document(uri, text)
          case Protocol.DidChangeTextDocument(uri, version, List(Protocol.TextDocumentContent(text))) =>
            update_document(uri, text)
          case Protocol.DidCloseTextDocument(uri) => channel.log("CLOSE " + uri)
          case Protocol.DidSaveTextDocument(uri) => channel.log("SAVE " + uri)
          case Protocol.Hover(id, uri, pos) =>
            channel.write(Protocol.Hover.reply(id, hover(uri, pos)))
          case _ => channel.log("### IGNORED")
        }
      }
      catch { case exn: Throwable => channel.log("*** ERROR: " + Exn.message(exn)) }
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
        case None => channel.log("### TERMINATE")
      }
    }
    loop()
  }
}
