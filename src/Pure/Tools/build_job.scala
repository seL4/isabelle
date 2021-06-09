/*  Title:      Pure/Tools/build_job.scala
    Author:     Makarius

Build job running prover process, with rudimentary PIDE session.
*/

package isabelle


import scala.collection.mutable


object Build_Job
{
  /* theory markup/messages from database */

  def read_theory(
    db_context: Sessions.Database_Context,
    resources: Resources,
    session: String,
    theory: String,
    unicode_symbols: Boolean = false): Option[Command] =
  {
    def read(name: String): Export.Entry =
      db_context.get_export(List(session), theory, name)

    def read_xml(name: String): XML.Body =
      YXML.parse_body(
        Symbol.output(unicode_symbols, UTF8.decode_permissive(read(name).uncompressed)),
        cache = db_context.cache)

    (read(Export.DOCUMENT_ID).text, split_lines(read(Export.FILES).text)) match {
      case (Value.Long(id), thy_file :: blobs_files) =>
        val node_name = resources.file_node(Path.explode(thy_file), theory = theory)

        val results =
          Command.Results.make(
            for (elem @ XML.Elem(Markup(_, Markup.Serial(i)), _) <- read_xml(Export.MESSAGES))
              yield i -> elem)

        val blobs =
          blobs_files.map(file =>
          {
            val path = Path.explode(file)
            val name = resources.file_node(path)
            val src_path = File.relative_path(node_name.master_dir_path, path).getOrElse(path)
            Command.Blob(name, src_path, None)
          })
        val blobs_xml =
          for (i <- (1 to blobs.length).toList)
            yield read_xml(Export.MARKUP + i)

        val blobs_info =
          Command.Blobs_Info(
            for { (Command.Blob(name, src_path, _), xml) <- blobs zip blobs_xml }
              yield {
                val text = XML.content(xml)
                val chunk = Symbol.Text_Chunk(text)
                val digest = SHA1.digest(Symbol.encode(text))
                Exn.Res(Command.Blob(name, src_path, Some((digest, chunk))))
              })

        val thy_xml = read_xml(Export.MARKUP)
        val thy_source = XML.content(thy_xml)

        val markups_index =
          Command.Markup_Index.markup :: blobs.map(Command.Markup_Index.blob)
        val markups =
          Command.Markups.make(
            for ((index, xml) <- markups_index.zip(thy_xml :: blobs_xml))
            yield index -> Markup_Tree.from_XML(xml))

        val command =
          Command.unparsed(thy_source, theory = true, id = id, node_name = node_name,
            blobs_info = blobs_info, results = results, markups = markups)
        Some(command)
      case _ => None
    }
  }


  /* print messages */

  def print_log(
    options: Options,
    session_name: String,
    theories: List[String] = Nil,
    verbose: Boolean = false,
    progress: Progress = new Progress,
    margin: Double = Pretty.default_margin,
    breakgain: Double = Pretty.default_breakgain,
    metric: Pretty.Metric = Symbol.Metric,
    unicode_symbols: Boolean = false): Unit =
  {
    val store = Sessions.store(options)
    val resources = Resources.empty
    val session = new Session(options, resources)

    using(store.open_database_context())(db_context =>
    {
      val result =
        db_context.input_database(session_name)((db, _) =>
        {
          val theories = store.read_theories(db, session_name)
          val errors = store.read_errors(db, session_name)
          store.read_build(db, session_name).map(info => (theories, errors, info.return_code))
        })
      result match {
        case None => error("Missing build database for session " + quote(session_name))
        case Some((used_theories, errors, rc)) =>
          theories.filterNot(used_theories.toSet) match {
            case Nil =>
            case bad => error("Unknown theories " + commas_quote(bad))
          }
          val print_theories =
            if (theories.isEmpty) used_theories else used_theories.filter(theories.toSet)
          for (thy <- print_theories) {
            val thy_heading = "\nTheory " + quote(thy) + ":"
            read_theory(db_context, resources, session_name, thy, unicode_symbols = unicode_symbols)
            match {
              case None => progress.echo(thy_heading + " MISSING")
              case Some(command) =>
                val snapshot = Document.State.init.snippet(command)
                val rendering = new Rendering(snapshot, options, session)
                val messages =
                  rendering.text_messages(Text.Range.full)
                    .filter(message => verbose || Protocol.is_exported(message.info))
                if (messages.nonEmpty) {
                  val line_document = Line.Document(command.source)
                  progress.echo(thy_heading)
                  for (Text.Info(range, elem) <- messages) {
                    val line = line_document.position(range.start).line1
                    val pos = Position.Line_File(line, command.node_name.node)
                    progress.echo(
                      Protocol.message_text(elem, heading = true, pos = pos,
                        margin = margin, breakgain = breakgain, metric = metric))
                  }
                }
            }
          }

          if (errors.nonEmpty) {
            val msg = Symbol.output(unicode_symbols, cat_lines(errors))
            progress.echo("\nBuild errors:\n" + Output.error_message_text(msg))
          }
          if (rc != 0) progress.echo("\n" + Process_Result.print_return_code(rc))
      }
    })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("log", "print messages from build database",
    Scala_Project.here, args =>
  {
    /* arguments */

    var unicode_symbols = false
    var theories: List[String] = Nil
    var margin = Pretty.default_margin
    var options = Options.init()
    var verbose = false

    val getopts = Getopts("""
Usage: isabelle log [OPTIONS] SESSION

  Options are:
    -T NAME      restrict to given theories (multiple options possible)
    -U           output Unicode symbols
    -m MARGIN    margin for pretty printing (default: """ + margin + """)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           print all messages, including information etc.

  Print messages from the build database of the given session, without any
  checks against current sources: results from a failed build can be
  printed as well.
""",
      "T:" -> (arg => theories = theories ::: List(arg)),
      "U" -> (_ => unicode_symbols = true),
      "m:" -> (arg => margin = Value.Double.parse(arg)),
      "o:" -> (arg => options = options + arg),
      "v" -> (_ => verbose = true))

    val more_args = getopts(args)
    val session_name =
      more_args match {
        case List(session_name) => session_name
        case _ => getopts.usage()
      }

    val progress = new Console_Progress()

    print_log(options, session_name, theories = theories, verbose = verbose, margin = margin,
      progress = progress, unicode_symbols = unicode_symbols)
  })
}

class Build_Job(progress: Progress,
  session_name: String,
  val info: Sessions.Info,
  deps: Sessions.Deps,
  store: Sessions.Store,
  do_store: Boolean,
  log: Logger,
  session_setup: (String, Session) => Unit,
  val numa_node: Option[Int],
  command_timings0: List[Properties.T])
{
  val options: Options = NUMA.policy_options(info.options, numa_node)

  private val sessions_structure = deps.sessions_structure

  private val future_result: Future[Process_Result] =
    Future.thread("build", uninterruptible = true) {
      val parent = info.parent.getOrElse("")
      val base = deps(parent)
      val result_base = deps(session_name)

      val env =
        Isabelle_System.settings() +
          ("ISABELLE_ML_DEBUGGER" -> options.bool("ML_debugger").toString)

      val is_pure = Sessions.is_pure(session_name)

      val use_prelude = if (is_pure) Thy_Header.ml_roots.map(_._1) else Nil

      val eval_store =
        if (do_store) {
          (if (info.theories.nonEmpty) List("ML_Heap.share_common_data ()") else Nil) :::
          List("ML_Heap.save_child " +
            ML_Syntax.print_string_bytes(File.platform_path(store.output_heap(session_name))))
        }
        else Nil

      val resources =
        new Resources(sessions_structure, base, log = log, command_timings = command_timings0)
      val session =
        new Session(options, resources) {
          override val cache: XML.Cache = store.cache

          override def build_blobs_info(name: Document.Node.Name): Command.Blobs_Info =
          {
            result_base.load_commands.get(name.expand) match {
              case Some(spans) =>
                val syntax = result_base.theory_syntax(name)
                Command.build_blobs_info(syntax, name, spans)
              case None => Command.Blobs_Info.none
            }
          }
        }

      object Build_Session_Errors
      {
        private val promise: Promise[List[String]] = Future.promise

        def result: Exn.Result[List[String]] = promise.join_result
        def cancel(): Unit = promise.cancel()
        def apply(errs: List[String]): Unit =
        {
          try { promise.fulfill(errs) }
          catch { case _: IllegalStateException => }
        }
      }

      val export_consumer =
        Export.consumer(store.open_database(session_name, output = true), store.cache)

      val stdout = new StringBuilder(1000)
      val stderr = new StringBuilder(1000)
      val command_timings = new mutable.ListBuffer[Properties.T]
      val theory_timings = new mutable.ListBuffer[Properties.T]
      val session_timings = new mutable.ListBuffer[Properties.T]
      val runtime_statistics = new mutable.ListBuffer[Properties.T]
      val task_statistics = new mutable.ListBuffer[Properties.T]

      def fun(
        name: String,
        acc: mutable.ListBuffer[Properties.T],
        unapply: Properties.T => Option[Properties.T]): (String, Session.Protocol_Function) =
      {
        name -> ((msg: Prover.Protocol_Output) =>
          unapply(msg.properties) match {
            case Some(props) => acc += props; true
            case _ => false
          })
      }

      session.init_protocol_handler(new Session.Protocol_Handler
        {
          override def exit(): Unit = Build_Session_Errors.cancel()

          private def build_session_finished(msg: Prover.Protocol_Output): Boolean =
          {
            val (rc, errors) =
              try {
                val (rc, errs) =
                {
                  import XML.Decode._
                  pair(int, list(x => x))(Symbol.decode_yxml(msg.text))
                }
                val errors =
                  for (err <- errs) yield {
                    val prt = Protocol_Message.expose_no_reports(err)
                    Pretty.string_of(prt, metric = Symbol.Metric)
                  }
                (rc, errors)
              }
              catch { case ERROR(err) => (2, List(err)) }

            session.protocol_command("Prover.stop", rc.toString)
            Build_Session_Errors(errors)
            true
          }

          private def loading_theory(msg: Prover.Protocol_Output): Boolean =
            msg.properties match {
              case Markup.Loading_Theory(Markup.Name(name)) =>
                progress.theory(Progress.Theory(name, session = session_name))
                false
              case _ => false
            }

          private def export(msg: Prover.Protocol_Output): Boolean =
            msg.properties match {
              case Protocol.Export(args) =>
                export_consumer(session_name, args, msg.chunk)
                true
              case _ => false
            }

          override val functions =
            List(
              Markup.Build_Session_Finished.name -> build_session_finished,
              Markup.Loading_Theory.name -> loading_theory,
              Markup.EXPORT -> export,
              fun(Markup.Theory_Timing.name, theory_timings, Markup.Theory_Timing.unapply),
              fun(Markup.Session_Timing.name, session_timings, Markup.Session_Timing.unapply),
              fun(Markup.Task_Statistics.name, task_statistics, Markup.Task_Statistics.unapply))
        })

      session.command_timings += Session.Consumer("command_timings")
        {
          case Session.Command_Timing(props) =>
            for {
              elapsed <- Markup.Elapsed.unapply(props)
              elapsed_time = Time.seconds(elapsed)
              if elapsed_time.is_relevant && elapsed_time >= options.seconds("command_timing_threshold")
            } command_timings += props.filter(Markup.command_timing_property)
        }

      session.runtime_statistics += Session.Consumer("ML_statistics")
        {
          case Session.Runtime_Statistics(props) => runtime_statistics += props
        }

      session.finished_theories += Session.Consumer[Document.Snapshot]("finished_theories")
        {
          case snapshot =>
            val rendering = new Rendering(snapshot, options, session)

            def export(name: String, xml: XML.Body, compress: Boolean = true): Unit =
            {
              val theory_name = snapshot.node_name.theory
              val args =
                Protocol.Export.Args(theory_name = theory_name, name = name, compress = compress)
              val bytes = Bytes(Symbol.encode(YXML.string_of_body(xml)))
              if (!bytes.is_empty) export_consumer(session_name, args, bytes)
            }
            def export_text(name: String, text: String, compress: Boolean = true): Unit =
              export(name, List(XML.Text(text)), compress = compress)

            for (command <- snapshot.snippet_command) {
              export_text(Export.DOCUMENT_ID, command.id.toString, compress = false)
            }

            export_text(Export.FILES,
              cat_lines(snapshot.node_files.map(_.symbolic.node)), compress = false)

            for (((_, xml), i) <- snapshot.xml_markup_blobs().zipWithIndex) {
              export(Export.MARKUP + (i + 1), xml)
            }
            export(Export.MARKUP, snapshot.xml_markup())
            export(Export.MESSAGES, snapshot.messages.map(_._1))

            val citations = Library.distinct(rendering.citations(Text.Range.full).map(_.info))
            export_text(Export.DOCUMENT_CITATIONS, cat_lines(citations))
        }

      session.all_messages += Session.Consumer[Any]("build_session_output")
        {
          case msg: Prover.Output =>
            val message = msg.message
            if (msg.is_system) resources.log(Protocol.message_text(message))

            if (msg.is_stdout) {
              stdout ++= Symbol.encode(XML.content(message))
            }
            else if (msg.is_stderr) {
              stderr ++= Symbol.encode(XML.content(message))
            }
            else if (msg.is_exit) {
              val err =
                "Prover terminated" +
                  (msg.properties match {
                    case Markup.Process_Result(result) => ": " + result.print_rc
                    case _ => ""
                  })
              Build_Session_Errors(List(err))
            }
          case _ =>
        }

      session_setup(session_name, session)

      val eval_main = Command_Line.ML_tool("Isabelle_Process.init_build ()" :: eval_store)

      val process =
        Isabelle_Process.start(session, options, sessions_structure, store,
          logic = parent, raw_ml_system = is_pure,
          use_prelude = use_prelude, eval_main = eval_main,
          cwd = info.dir.file, env = env)

      val build_errors =
        Isabelle_Thread.interrupt_handler(_ => process.terminate()) {
          Exn.capture { process.await_startup() } match {
            case Exn.Res(_) =>
              val resources_yxml = resources.init_session_yxml
              val args_yxml =
                YXML.string_of_body(
                  {
                    import XML.Encode._
                    pair(string, list(pair(Options.encode, list(pair(string, properties)))))(
                      (session_name, info.theories))
                  })
              session.protocol_command("build_session", resources_yxml, args_yxml)
              Build_Session_Errors.result
            case Exn.Exn(exn) => Exn.Res(List(Exn.message(exn)))
          }
        }

      val process_result =
        Isabelle_Thread.interrupt_handler(_ => process.terminate()) { process.await_shutdown() }

      session.stop()

      val export_errors =
        export_consumer.shutdown(close = true).map(Output.error_message_text)

      val (document_output, document_errors) =
        try {
          if (build_errors.isInstanceOf[Exn.Res[_]] && process_result.ok && info.documents.nonEmpty) {
            using(store.open_database_context())(db_context =>
              {
                val documents =
                  Document_Build.build_documents(
                    Document_Build.context(session_name, deps, db_context, progress = progress),
                    output_sources = info.document_output,
                    output_pdf = info.document_output)
                db_context.output_database(session_name)(db =>
                  documents.foreach(_.write(db, session_name)))
                (documents.flatMap(_.log_lines), Nil)
              })
          }
          else (Nil, Nil)
        }
        catch {
          case exn: Document_Build.Build_Error => (exn.log_lines, List(exn.message))
          case Exn.Interrupt.ERROR(msg) => (Nil, List(msg))
        }

      val result =
      {
        val theory_timing =
          theory_timings.iterator.map(
            { case props @ Markup.Name(name) => name -> props }).toMap
        val used_theory_timings =
          for { (name, _) <- deps(session_name).used_theories }
            yield theory_timing.getOrElse(name.theory, Markup.Name(name.theory))

        val more_output =
          Library.trim_line(stdout.toString) ::
            command_timings.toList.map(Protocol.Command_Timing_Marker.apply) :::
            used_theory_timings.map(Protocol.Theory_Timing_Marker.apply) :::
            session_timings.toList.map(Protocol.Session_Timing_Marker.apply) :::
            runtime_statistics.toList.map(Protocol.ML_Statistics_Marker.apply) :::
            task_statistics.toList.map(Protocol.Task_Statistics_Marker.apply) :::
            document_output

        process_result.output(more_output)
          .error(Library.trim_line(stderr.toString))
          .errors_rc(export_errors ::: document_errors)
      }

      build_errors match {
        case Exn.Res(build_errs) =>
          val errs = build_errs ::: document_errors
          if (errs.isEmpty) result
          else {
            result.error_rc.output(
              errs.flatMap(s => split_lines(Output.error_message_text(s))) :::
                errs.map(Protocol.Error_Message_Marker.apply))
          }
        case Exn.Exn(Exn.Interrupt()) =>
          if (result.ok) result.copy(rc = Exn.Interrupt.return_code) else result
        case Exn.Exn(exn) => throw exn
      }
    }

  def terminate(): Unit = future_result.cancel()
  def is_finished: Boolean = future_result.is_finished

  private val timeout_request: Option[Event_Timer.Request] =
  {
    if (info.timeout_ignored) None
    else Some(Event_Timer.request(Time.now() + info.timeout) { terminate() })
  }

  def join: (Process_Result, Option[String]) =
  {
    val result1 = future_result.join

    val was_timeout =
      timeout_request match {
        case None => false
        case Some(request) => !request.cancel()
      }

    val result2 =
      if (result1.ok) result1
      else if (was_timeout) result1.error(Output.error_message_text("Timeout")).timeout_rc
      else if (result1.interrupted) result1.error(Output.error_message_text("Interrupt"))
      else result1

    val heap_digest =
      if (result2.ok && do_store && store.output_heap(session_name).is_file)
        Some(Sessions.write_heap_digest(store.output_heap(session_name)))
      else None

    (result2, heap_digest)
  }
}
