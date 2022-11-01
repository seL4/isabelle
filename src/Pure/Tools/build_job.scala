/*  Title:      Pure/Tools/build_job.scala
    Author:     Makarius

Build job running prover process, with rudimentary PIDE session.
*/

package isabelle


import scala.collection.mutable
import scala.util.matching.Regex


object Build_Job {
  /* theory markup/messages from session database */

  def read_theory(
    theory_context: Export.Theory_Context,
    unicode_symbols: Boolean = false
  ): Option[Document.Snapshot] = {
    def read(name: String): Export.Entry = theory_context(name, permissive = true)

    def read_xml(name: String): XML.Body =
      YXML.parse_body(
        Symbol.output(unicode_symbols, UTF8.decode_permissive(read(name).uncompressed)),
        cache = theory_context.cache)

    for {
      id <- theory_context.document_id()
      (thy_file, blobs_files) <- theory_context.files(permissive = true)
    }
    yield {
      val master_dir =
        Thy_Header.split_file_name(thy_file) match {
          case Some((dir, _)) => dir
          case None => error("Cannot determine theory master directory: " + quote(thy_file))
        }
      val node_name =
        Document.Node.Name(thy_file, master_dir = master_dir, theory = theory_context.theory)

      val results =
        Command.Results.make(
          for (elem @ XML.Elem(Markup(_, Markup.Serial(i)), _) <- read_xml(Export.MESSAGES))
            yield i -> elem)

      val blobs =
        blobs_files.map { file =>
          val name = Document.Node.Name(file)
          val path = Path.explode(file)
          val src_path = File.relative_path(node_name.master_dir_path, path).getOrElse(path)
          Command.Blob(name, src_path, None)
        }
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

      Document.State.init.snippet(command)
    }
  }


  /* print messages */

  def print_log(
    options: Options,
    sessions: List[String],
    theories: List[String] = Nil,
    message_head: List[Regex] = Nil,
    message_body: List[Regex] = Nil,
    verbose: Boolean = false,
    progress: Progress = new Progress,
    margin: Double = Pretty.default_margin,
    breakgain: Double = Pretty.default_breakgain,
    metric: Pretty.Metric = Symbol.Metric,
    unicode_symbols: Boolean = false,
    show_theory_timings: Boolean = false,
    show_command_timings: Boolean = false,
    show_session_timing: Boolean = false,
    sort_timings: Boolean = false
  ): Unit = {
    val store = Sessions.store(options)
    val session = new Session(options, Resources.empty)

    def check(filter: List[Regex], make_string: => String): Boolean =
      filter.isEmpty || {
        val s = Output.clean_yxml(make_string)
        filter.forall(r => r.findFirstIn(Output.clean_yxml(s)).nonEmpty)
      }

    def print(session_name: String): Unit = {
      using(Export.open_session_context0(store, session_name)) { session_context =>
        val result =
          for {
            db <- session_context.session_db()
            theories = store.read_theories(db, session_name)
            errors = store.read_errors(db, session_name)
            thy_timings = store.read_theory_timings(db, session_name)
            command_timings = store.read_command_timings(db, session_name)
            session_timing = store.read_session_timing(db, session_name)
            info <- store.read_build(db, session_name)
          } yield (theories, errors, thy_timings, command_timings, session_timing, info.return_code)
        result match {
          case None => store.error_database(session_name)
          case Some((used_theories, errors, thy_timings, command_timings, session_timing, rc)) =>
            theories.filterNot(used_theories.toSet) match {
              case Nil =>
              case bad => error("Unknown theories " + commas_quote(bad))
            }
            if (verbose || !(show_command_timings || show_theory_timings || show_session_timing)) {
              val print_theories =
                if (theories.isEmpty) used_theories else used_theories.filter(theories.toSet)

              for (thy <- print_theories) {
                val thy_heading = "\nTheory " + quote(thy) + " (in " + session_name + ")" + ":"

                read_theory(session_context.theory(thy), unicode_symbols = unicode_symbols) match {
                  case None => progress.echo(thy_heading + " MISSING")
                  case Some(snapshot) =>
                    val rendering = new Rendering(snapshot, options, session)
                    val messages =
                      rendering.text_messages(Text.Range.full)
                        .filter(message => verbose || Protocol.is_exported(message.info))
                    if (messages.nonEmpty) {
                      val line_document = Line.Document(snapshot.source)
                      val buffer = new mutable.ListBuffer[String]
                      for (Text.Info(range, elem) <- messages) {
                        val line = line_document.position(range.start).line1
                        val pos = Position.Line_File(line, snapshot.node_name.node)
                        def message_text: String =
                          Protocol.message_text(elem, heading = true, pos = pos,
                            margin = margin, breakgain = breakgain, metric = metric)
                        val ok =
                          check(message_head, Protocol.message_heading(elem, pos)) &&
                          check(message_body, XML.content(Pretty.unformatted(List(elem))))
                        if (ok) buffer += message_text
                      }
                      if (buffer.nonEmpty) {
                        progress.echo(thy_heading)
                        buffer.foreach(progress.echo)
                      }
                    }
                }
              }
            }

            if (show_theory_timings || verbose) {
              val typed_thy_timings =
                thy_timings.map({
                  case (_, name)::(_, elapsed)::(_, cpu)::(_, gc)::_ =>
                    val e = Time.seconds(elapsed.toDouble)
                    val c = Time.seconds(cpu.toDouble)
                    val g = Time.seconds(gc.toDouble)
                    (name, Timing(e, c, g), e)
                  case bad => ("bad timing data", Timing.zero, Time.zero)
                })

              val sorted_timings =
                if (sort_timings) typed_thy_timings.sortWith({ case ((_, _, a), (_, _, b)) => a < b })
                else typed_thy_timings

              progress.echo("\nTheory timings:")
              for ((name, timing, _) <- sorted_timings) {
                progress.echo(name + ": " + timing)
              }
            }

            if (show_command_timings || verbose) {
              val typed_command_timings =
                command_timings.map({
                  case (_, name)::(_, offset)::(_, file)::(_, time)::_ =>
                    (name, offset, file, Time.seconds(time.toDouble))
                  case bad => ("bad timing data", 0, "", Time.zero)
                })

              val sorted_com_timings =
                if (sort_timings) typed_command_timings.sortWith({ case ((_, _, _, a), (_, _, _, b)) => a < b })
                else typed_command_timings

              progress.echo("\nCommand timings:")
              for (timing <- sorted_com_timings) {
                timing match {
                  case (name, offset, file, t) =>
                    progress.echo(quote(name) + " " + t + "s ["+file+"::"+offset+"]")
                }
              }
            }

            if (show_session_timing || verbose) {
              session_timing match {
                case (_, threads)::(_, elapsed)::(_, cpu)::(_, gc)::_ =>
                  val e = Time.seconds(elapsed.toDouble)
                  val c = Time.seconds(cpu.toDouble)
                  val g = Time.seconds(gc.toDouble)
                  progress.echo("\nSession timing " + session_name + ": " +
                                Timing(e,c,g).message_resources +
                                ", " + threads + " threads")
                case bad => progress.echo("\nBad session timing data")
              }
            }

            if (errors.nonEmpty) {
              val msg = Symbol.output(unicode_symbols, cat_lines(errors))
              progress.echo("\nBuild errors:\n" + Output.error_message_text(msg))
            }
            if (rc != Process_Result.RC.ok) {
              progress.echo("\n" + Process_Result.RC.print_long(rc))
            }
        }
      }
    }

    val errors = new mutable.ListBuffer[String]
    for (session_name <- sessions) {
      Exn.interruptible_capture(print(session_name)) match {
        case Exn.Res(_) =>
        case Exn.Exn(exn) => errors += Exn.message(exn)
      }
    }
    if (errors.nonEmpty) error(cat_lines(errors.toList))
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("log", "print messages from build database",
    Scala_Project.here,
    { args =>
      /* arguments */

      var message_head = List.empty[Regex]
      var message_body = List.empty[Regex]
      var unicode_symbols = false
      var theories: List[String] = Nil
      var margin = Pretty.default_margin
      var options = Options.init()
      var verbose = false
      var command_timings = false
      var theory_timings = false
      var session_timing = false
      var sort_timings = false

      val getopts = Getopts("""
Usage: isabelle log [OPTIONS] [SESSIONS ...]

  Options are:
    -H REGEX     filter messages by matching against head
    -M REGEX     filter messages by matching against body
    -S           sort timing output by elapsed time
    -T NAME      restrict to given theories (multiple options possible)
    -U           output Unicode symbols
    -c           show command timings
    -m MARGIN    margin for pretty printing (default: """ + margin + """)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -s           show session timing
    -t           show theory timings
    -v           print all messages, including information etc.

  Print messages from the build database of the given sessions, without any
  checks against current sources nor session structure: results from old
  sessions or failed builds can be printed as well.

  Multiple options -H and -M are conjunctive: all given patterns need to
  match. Patterns match any substring, but ^ or $ may be used to match the
  start or end explicitly.
""",
        "H:" -> (arg => message_head = message_head ::: List(arg.r)),
        "M:" -> (arg => message_body = message_body ::: List(arg.r)),
        "S" -> (_ => sort_timings = true),
        "T:" -> (arg => theories = theories ::: List(arg)),
        "U" -> (_ => unicode_symbols = true),
        "c" -> (_ => command_timings = true),
        "m:" -> (arg => margin = Value.Double.parse(arg)),
        "o:" -> (arg => options = options + arg),
        "s" -> (_ => session_timing = true),
        "t" -> (_ => theory_timings = true),
        "v" -> (_ => verbose = true))

      val sessions = getopts(args)

      val progress = new Console_Progress()

      if (sessions.isEmpty) progress.echo_warning("No sessions to print")
      else {
        print_log(options, sessions, theories = theories, message_head = message_head,
          message_body = message_body, verbose = verbose, margin = margin, progress = progress,
          unicode_symbols = unicode_symbols, show_theory_timings = theory_timings,
          show_command_timings = command_timings, show_session_timing = session_timing,
          sort_timings = sort_timings)
      }
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
  command_timings0: List[Properties.T]
) {
  val options: Options = NUMA.policy_options(info.options, numa_node)

  private val sessions_structure = deps.sessions_structure

  private val future_result: Future[Process_Result] =
    Future.thread("build", uninterruptible = true) {
      val parent = info.parent.getOrElse("")
      val base = deps(parent)
      val result_base = deps(session_name)

      val env =
        Isabelle_System.settings(
          List("ISABELLE_ML_DEBUGGER" -> options.bool("ML_debugger").toString))

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
          override val cache: Term.Cache = store.cache

          override def build_blobs_info(name: Document.Node.Name): Command.Blobs_Info = {
            result_base.load_commands.get(name.expand) match {
              case Some(spans) =>
                val syntax = result_base.theory_syntax(name)
                Command.build_blobs_info(syntax, name, spans)
              case None => Command.Blobs_Info.none
            }
          }
        }

      object Build_Session_Errors {
        private val promise: Promise[List[String]] = Future.promise

        def result: Exn.Result[List[String]] = promise.join_result
        def cancel(): Unit = promise.cancel()
        def apply(errs: List[String]): Unit = {
          try { promise.fulfill(errs) }
          catch { case _: IllegalStateException => }
        }
      }

      val export_consumer =
        Export.consumer(store.open_database(session_name, output = true), store.cache,
          progress = progress)

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
        unapply: Properties.T => Option[Properties.T]
      ): (String, Session.Protocol_Function) = {
        name -> ((msg: Prover.Protocol_Output) =>
          unapply(msg.properties) match {
            case Some(props) => acc += props; true
            case _ => false
          })
      }

      session.init_protocol_handler(new Session.Protocol_Handler {
          override def exit(): Unit = Build_Session_Errors.cancel()

          private def build_session_finished(msg: Prover.Protocol_Output): Boolean = {
            val (rc, errors) =
              try {
                val (rc, errs) = {
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
              catch { case ERROR(err) => (Process_Result.RC.failure, List(err)) }

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

          private def export_(msg: Prover.Protocol_Output): Boolean =
            msg.properties match {
              case Protocol.Export(args) =>
                export_consumer.make_entry(session_name, args, msg.chunk)
                true
              case _ => false
            }

          override val functions: Session.Protocol_Functions =
            List(
              Markup.Build_Session_Finished.name -> build_session_finished,
              Markup.Loading_Theory.name -> loading_theory,
              Markup.EXPORT -> export_,
              fun(Markup.Theory_Timing.name, theory_timings, Markup.Theory_Timing.unapply),
              fun(Markup.Session_Timing.name, session_timings, Markup.Session_Timing.unapply),
              fun(Markup.Task_Statistics.name, task_statistics, Markup.Task_Statistics.unapply))
        })

      session.command_timings += Session.Consumer("command_timings") {
        case Session.Command_Timing(props) =>
          for {
            elapsed <- Markup.Elapsed.unapply(props)
            elapsed_time = Time.seconds(elapsed)
            if elapsed_time.is_relevant && elapsed_time >= options.seconds("command_timing_threshold")
          } command_timings += props.filter(Markup.command_timing_property)
      }

      session.runtime_statistics += Session.Consumer("ML_statistics") {
        case Session.Runtime_Statistics(props) => runtime_statistics += props
      }

      session.finished_theories += Session.Consumer[Document.Snapshot]("finished_theories") {
        case snapshot =>
          if (!progress.stopped) {
            val rendering = new Rendering(snapshot, options, session)

            def export_(name: String, xml: XML.Body, compress: Boolean = true): Unit = {
              if (!progress.stopped) {
                val theory_name = snapshot.node_name.theory
                val args =
                  Protocol.Export.Args(theory_name = theory_name, name = name, compress = compress)
                val body = Bytes(Symbol.encode(YXML.string_of_body(xml)))
                export_consumer.make_entry(session_name, args, body)
              }
            }
            def export_text(name: String, text: String, compress: Boolean = true): Unit =
              export_(name, List(XML.Text(text)), compress = compress)

            for (command <- snapshot.snippet_command) {
              export_text(Export.DOCUMENT_ID, command.id.toString, compress = false)
            }

            export_text(Export.FILES,
              cat_lines(snapshot.node_files.map(_.path.implode_symbolic)), compress = false)

            for (((_, xml), i) <- snapshot.xml_markup_blobs().zipWithIndex) {
              export_(Export.MARKUP + (i + 1), xml)
            }
            export_(Export.MARKUP, snapshot.xml_markup())
            export_(Export.MESSAGES, snapshot.messages.map(_._1))

            val citations = Library.distinct(rendering.citations(Text.Range.full).map(_.info))
            export_text(Export.DOCUMENT_CITATIONS, cat_lines(citations))
          }
      }

      session.all_messages += Session.Consumer[Any]("build_session_output") {
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
              val encode_options: XML.Encode.T[Options] =
                options => session.prover_options(options).encode
              val args_yxml =
                YXML.string_of_body(
                  {
                    import XML.Encode._
                    pair(string, list(pair(encode_options, list(pair(string, properties)))))(
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
            using(Export.open_database_context(store)) { database_context =>
              val documents =
                using(database_context.open_session(deps.base_info(session_name))) {
                  session_context =>
                    Document_Build.build_documents(
                      Document_Build.context(session_context, progress = progress),
                      output_sources = info.document_output,
                      output_pdf = info.document_output)
                }
              using(database_context.open_database(session_name, output = true))(session_database =>
                documents.foreach(_.write(session_database.db, session_name)))
              (documents.flatMap(_.log_lines), Nil)
            }
          }
          else (Nil, Nil)
        }
        catch {
          case exn: Document_Build.Build_Error => (exn.log_lines, List(exn.message))
          case Exn.Interrupt.ERROR(msg) => (Nil, List(msg))
        }

      val result = {
        val theory_timing =
          theory_timings.iterator.flatMap(
            {
              case props @ Markup.Name(name) => Some(name -> props)
              case _ => None
            }).toMap
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
          if (errs.nonEmpty) {
            result.error_rc.output(
              errs.flatMap(s => split_lines(Output.error_message_text(s))) :::
                errs.map(Protocol.Error_Message_Marker.apply))
          }
          else if (progress.stopped && result.ok) result.copy(rc = Process_Result.RC.interrupt)
          else result
        case Exn.Exn(Exn.Interrupt()) =>
          if (result.ok) result.copy(rc = Process_Result.RC.interrupt)
          else result
        case Exn.Exn(exn) => throw exn
      }
    }

  def terminate(): Unit = future_result.cancel()
  def is_finished: Boolean = future_result.is_finished

  private val timeout_request: Option[Event_Timer.Request] = {
    if (info.timeout_ignored) None
    else Some(Event_Timer.request(Time.now() + info.timeout) { terminate() })
  }

  def join: (Process_Result, Option[String]) = {
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
