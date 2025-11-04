/*  Title:      Pure/Build/build_job.scala
    Author:     Makarius

Build job running prover process, with rudimentary PIDE session.
*/

package isabelle


import java.io.BufferedWriter
import java.nio.file.Files


trait Build_Job {
  def cancel(): Unit = ()
  def is_finished: Boolean = false
  def join: Build_Job.Result = Build_Job.no_result
}

object Build_Job {
  sealed case class Result(process_result: Process_Result, output_shasum: SHA1.Shasum)
  val no_result: Result = Result(Process_Result.undefined, SHA1.no_shasum)


  /* build session */

  def start_session(
    build_context: Build.Context,
    session_context: Session_Context,
    progress: Progress,
    log: Logger,
    server: SSH.Server,
    session_background: Sessions.Background,
    sources_shasum: SHA1.Shasum,
    input_shasum: SHA1.Shasum,
    node_info: Host.Node_Info,
    store_heap: Boolean
  ): Session_Job = {
    new Session_Job(build_context, session_context, progress, log, server,
      session_background, sources_shasum, input_shasum, node_info, store_heap)
  }

  object Session_Context {
    def load(
      database_server: Option[SQL.Database],
      build_uuid: String,
      name: String,
      deps: List[String],
      ancestors: List[String],
      session_prefs: String,
      sources_shasum: SHA1.Shasum,
      timeout: Time,
      store: Store,
      progress: Progress = new Progress
    ): Session_Context = {
      def default: Session_Context =
        Session_Context(
          name, deps, ancestors, session_prefs, sources_shasum, timeout,
          Time.zero, Bytes.empty, build_uuid)

      def read(db: SQL.Database): Session_Context = {
        def ignore_error(msg: String) = {
          progress.echo_warning(
            "Ignoring bad database " + db + " for session " + quote(name) +
            if_proper(msg, ":\n" + msg))
          default
        }
        try {
          val command_timings = store.read_command_timings(db, name)
          val elapsed = Time.seconds(Markup.Elapsed.get(store.read_session_timing(db, name)))
          new Session_Context(
            name, deps, ancestors, session_prefs, sources_shasum, timeout,
            elapsed, command_timings, build_uuid)
        }
        catch {
          case ERROR(msg) => ignore_error(msg)
          case exn: java.lang.Error => ignore_error(Exn.message(exn))
          case _: XML.Error => ignore_error("XML.Error")
        }
      }

      database_server match {
        case Some(db) => if (store.session_info_exists(db)) read(db) else default
        case None => using_option(store.try_open_database(name))(read) getOrElse default
      }
    }
  }

  sealed case class Session_Context(
    name: String,
    deps: List[String],
    ancestors: List[String],
    session_prefs: String,
    sources_shasum: SHA1.Shasum,
    timeout: Time,
    old_time: Time,
    old_command_timings_blob: Bytes,
    build_uuid: String
  ) extends Name.T

  abstract class Build_Session(progress: Progress) extends Session {
    /* additional process output */

    private val process_output_file = Isabelle_System.tmp_file("process_output")
    private var process_output_writer: Option[BufferedWriter] = None

    def read_process_output(): List[String] = synchronized {
      require(process_output_writer.isEmpty, "read_process_output")
      using(Files.newBufferedReader(process_output_file.toPath))(File.read_lines(_, _ => ()))
    }

    def write_process_output(str: String): Unit = synchronized {
      require(process_output_writer.isDefined, "write_process_output")
      process_output_writer.get.write(str)
      process_output_writer.get.write("\n")
    }

    def start_process_output(): Unit = synchronized {
      require(process_output_writer.isEmpty, "start_process_output")
      process_output_file.delete
      process_output_writer = Some(File.writer(process_output_file))
    }

    def stop_process_output(): Unit = synchronized {
      process_output_writer.foreach(_.close())
      process_output_writer = None
    }

    def clean_process_output(): Unit = synchronized {
      process_output_file.delete
    }


    /* options */

    val build_progress_delay: Time = session_options.seconds("build_progress_delay")
    val build_timing_threshold: Time = session_options.seconds("build_timing_threshold")
    val editor_timing_threshold: Time = session_options.seconds("editor_timing_threshold")


    /* errors */

    private val build_errors: Promise[List[String]] = Future.promise

    def errors_result(): Exn.Result[List[String]] = build_errors.join_result
    def errors_cancel(): Unit = build_errors.cancel()
    def errors(errs: List[String]): Unit = {
      try { build_errors.fulfill(errs) }
      catch { case _: IllegalStateException => }
    }


    /* document nodes --- session theories */

    def nodes_domain: List[Document.Node.Name]

    private var nodes_changed = Set.empty[Document_ID.Generic]
    private var nodes_status = Document_Status.Nodes_Status.empty

    private def nodes_status_progress(state: Document.State = get_state()): Unit = {
      val result =
        synchronized {
          for (id <- state.progress_theories if !nodes_changed(id)) nodes_changed += id
          val nodes_status1 =
            nodes_changed.foldLeft(nodes_status)({ case (status, state_id) =>
              state.theory_snapshot(state_id, build_blobs) match {
                case None => status
                case Some(snapshot) =>
                  Exn.Interrupt.expose()
                  status.update_node(progress.now(),
                    snapshot.state, snapshot.version, snapshot.node_name,
                    threshold = editor_timing_threshold)
              }
            })
          val result =
            if (nodes_changed.isEmpty) None
            else {
              Some(Progress.Nodes_Status(
                nodes_domain, nodes_status1,
                session = resources.session_background.session_name,
                old = Some(nodes_status)))
            }

          nodes_changed = Set.empty
          nodes_status = nodes_status1

          result
        }
      result.foreach(progress.nodes_status)
    }

    private lazy val nodes_delay: Delay =
      Delay.first(build_progress_delay) { nodes_status_progress(); nodes_delay.invoke() }

    def nodes_status_exit(state: Document.State): Unit = synchronized {
      nodes_delay.revoke()
      nodes_status_progress(state = state)
      progress.nodes_status(Progress.Nodes_Status.empty(resources.session_background.session_name))
    }

    override def start(start_prover: Prover.Receiver => Prover): Unit = {
      start_process_output()
      super.start(start_prover)
    }

    def command_timing(state_id: Document_ID.Generic, props: Properties.T): Unit = synchronized {
      val elapsed = Time.seconds(Markup.Elapsed.get(props))
      if (elapsed.is_notable(build_timing_threshold)) {
        write_process_output(
          Protocol.Command_Timing_Marker(props.filter(Markup.command_timing_export)))
      }

      nodes_changed += state_id
      nodes_delay.invoke()
    }
  }

  class Session_Job private[Build_Job](
    build_context: Build.Context,
    session_context: Session_Context,
    progress: Progress,
    log: Logger,
    server: SSH.Server,
    session_background: Sessions.Background,
    sources_shasum: SHA1.Shasum,
    input_shasum: SHA1.Shasum,
    node_info: Host.Node_Info,
    store_heap: Boolean
  ) extends Build_Job {
    def session_name: String = session_background.session_name

    private val future_result: Future[Result] =
      Future.thread("build", uninterruptible = true) {
        val info = session_background.sessions_structure(session_name)
        val options = Host.node_options(info.options, node_info)
        val store = build_context.store

        using_optional(store.maybe_open_database_server(server = server)) { database_server =>
          store.clean_output(database_server, session_name, session_init = true)

          val session_sources =
            Store.Sources.load(session_background.base, cache = store.cache.compress)

          val env =
            Isabelle_System.Settings.env(
              List("ISABELLE_ML_DEBUGGER" -> options.bool("ML_debugger").toString))

          val session_heaps =
            session_background.info.parent match {
              case None => Nil
              case Some(logic) => store.session_heaps(session_background, logic = logic)
            }

          val use_prelude = if (session_heaps.isEmpty) Thy_Header.ml_roots.map(_._1) else Nil

          val eval_store =
            if (store_heap) {
              (if (info.theories.nonEmpty) List("ML_Heap.share_common_data ()") else Nil) :::
              List("ML_Heap.save_child " +
                ML_Syntax.print_string_bytes(File.platform_path(store.output_heap(session_name))))
            }
            else Nil

          def session_blobs(node_name: Document.Node.Name): List[(Command.Blob, Document.Blobs.Item)] =
            session_background.base.theory_load_commands.get(node_name.theory) match {
              case None => Nil
              case Some(load_commands) =>
                val syntax = session_background.base.theory_syntax(node_name)
                val master_dir = Path.explode(node_name.master_dir)
                for {
                  (command_span, command_offset) <- load_commands
                  file <- command_span.loaded_files(syntax).files
                } yield {
                    val src_path = Path.explode(file)
                    val blob_name = Document.Node.Name(File.symbolic_path(master_dir + src_path))

                    val bytes = session_sources(blob_name.node).bytes
                    val text = bytes.text
                    val chunk = Symbol.Text_Chunk(text)
                    val content = Some((SHA1.digest(bytes), chunk))

                    Command.Blob(command_offset, blob_name, src_path, content) ->
                      Document.Blobs.Item(bytes, text, chunk, command_offset = command_offset)
                  }
            }


          /* session */

          val session =
            new Build_Session(progress) {
              override def session_options: Options = options

              override val store: Store = build_context.store

              override val resources: Resources =
                new Resources(session_background, log = log,
                  command_timings =
                    Properties.uncompress(session_context.old_command_timings_blob, cache = cache))

              override def build_blobs_info(node_name: Document.Node.Name): Command.Blobs_Info =
                Command.Blobs_Info.make(session_blobs(node_name))

              override def build_blobs(node_name: Document.Node.Name): Document.Blobs =
                Document.Blobs.make(session_blobs(node_name))

              override val nodes_domain: List[Document.Node.Name] =
                session_background.base.used_theories.map(_._1.symbolic_path)
            }

          val export_consumer =
            Export.consumer(store.open_database(session_name, output = true, server = server),
              store.cache, progress = progress)

          // mutable state: session.synchronized
          val stdout = new StringBuilder(1000)
          val stderr = new StringBuilder(1000)

          def fun(
            name: String,
            marker: Protocol_Message.Marker,
            unapply: Properties.T => Option[Properties.T]
          ): (String, Session.Protocol_Function) = {
            name -> ((msg: Prover.Protocol_Output) =>
              unapply(msg.properties) match {
                case Some(props) => session.write_process_output(marker(props)); true
                case _ => false
              })
          }

          session.init_protocol_handler(new Session.Protocol_Handler {
              override def exit(exit_state: Document.State): Unit = {
                session.nodes_status_exit(exit_state)
                session.errors_cancel()
              }

              private def build_session_finished(msg: Prover.Protocol_Output): Boolean = {
                val (rc, errors) =
                  try {
                    val (rc, errs) = {
                      import XML.Decode._
                      pair(int, list(self))(Symbol.decode_yxml(msg.text))
                    }
                    val errors =
                      for (err <- errs) yield {
                        Pretty.string_of(err, metric = Symbol.Metric, pure = true)
                      }
                    (rc, errors)
                  }
                  catch { case ERROR(err) => (Process_Result.RC.failure, List(err)) }

                session.protocol_command("Prover.stop", XML.Encode.int(rc))
                session.errors(errors)
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
                  fun(Markup.Session_Timing.name,
                    Protocol.Session_Timing_Marker, Markup.Session_Timing.unapply),
                  fun(Markup.Task_Statistics.name,
                    Protocol.Task_Statistics_Marker, Markup.Task_Statistics.unapply))
            })

          session.command_timings += Session.Consumer("command_timings") {
            case Session.Command_Timing(state_id, props) => session.command_timing(state_id, props)
          }

          session.runtime_statistics += Session.Consumer("ML_statistics") {
            case Session.Runtime_Statistics(props) =>
              session.write_process_output(Protocol.ML_Statistics_Marker(props))
          }

          session.finished_theories += Session.Consumer[Document.Snapshot]("finished_theories") {
            case snapshot =>
              if (!progress.stopped) {
                def export_(name: String, xml: XML.Body, compress: Boolean = true): Unit = {
                  if (!progress.stopped) {
                    val theory_name = snapshot.node_name.theory
                    val args =
                      Protocol.Export.Args(
                        theory_name = theory_name, name = name, compress = compress)
                    val body = YXML.bytes_of_body(xml, recode = Symbol.encode)
                    export_consumer.make_entry(session_name, args, body)
                  }
                }
                def export_text(name: String, text: String, compress: Boolean = true): Unit =
                  export_(name, List(XML.Text(text)), compress = compress)

                assert(snapshot.snippet_commands.length == 1)
                for (command <- snapshot.snippet_commands) {
                  export_text(Export.DOCUMENT_ID, command.id.toString, compress = false)
                }

                export_(Export.FILES,
                  {
                    import XML.Encode._
                    list(pair(int, string))(snapshot.node_export_files)
                  })

                for ((blob_name, i) <- snapshot.node_files.tail.zipWithIndex) {
                  val xml = snapshot.switch(blob_name).xml_markup()
                  export_(Export.MARKUP + (i + 1), xml)
                }
                export_(Export.MARKUP, snapshot.xml_markup())
                export_(Export.MESSAGES, snapshot.messages.map(_._1))
              }
          }

          session.all_messages += Session.Consumer[Any]("build_session_output") {
            case msg: Prover.Output =>
              val message = msg.message
              if (msg.is_system) session.resources.log(Protocol.message_text(message))

              if (msg.is_stdout) {
                session.synchronized { stdout ++= Symbol.encode(XML.content(message)) }
              }
              else if (msg.is_stderr) {
                session.synchronized { stderr ++= Symbol.encode(XML.content(message)) }
              }
              else if (msg.is_exit) {
                val err =
                  "Prover terminated" +
                    (msg.properties match {
                      case Markup.Process_Result(result) => ": " + result.print_rc
                      case _ => ""
                    })
                session.errors(List(err))
              }
            case _ =>
          }

          build_context.session_setup(session_name, session)

          val eval_main = Command_Line.ML_tool("Isabelle_Process.init_build ()" :: eval_store)


          /* process */

          val process =
            Isabelle_Process.start(options, session, session_background, session_heaps,
              use_prelude = use_prelude, eval_main = eval_main, cwd = info.dir, env = env)

          val timeout_request: Option[Event_Timer.Request] =
            if (info.timeout_ignored) None
            else Some(Event_Timer.request(Time.now() + info.timeout) { process.terminate() })

          val build_errors =
            Isabelle_Thread.interrupt_handler(_ => process.terminate()) {
              Exn.capture { process.await_startup() } match {
                case Exn.Res(_) =>
                  val resources_xml = session.resources.init_session_xml
                  val encode_options: XML.Encode.T[Options] =
                    options => session.prover_options(options).encode
                  val args_xml =
                    {
                      import XML.Encode._
                      pair(string, list(pair(encode_options, list(pair(string, properties)))))(
                        (session_name, info.theories))
                    }
                  session.protocol_command("build_session", resources_xml, args_xml)
                  session.errors_result()
                case Exn.Exn(exn) => Exn.Res(List(Exn.message(exn)))
              }
            }

          val result0 =
            Isabelle_Thread.interrupt_handler(_ => process.terminate()) { process.await_shutdown() }

          val was_timeout =
            timeout_request match {
              case None => false
              case Some(request) => !request.cancel()
            }

          session.stop()
          session.stop_process_output()

          val export_errors =
            export_consumer.shutdown(close = true).map(Output.error_message_text)

          val (document_output, document_errors) =
            try {
              if (Exn.is_res(build_errors) && result0.ok && info.documents.nonEmpty) {
                using(Export.open_database_context(store, server = server)) { database_context =>
                  val documents =
                    using(database_context.open_session(session_background)) {
                      session_context =>
                        Document_Build.build_documents(
                          Document_Build.context(session_context, progress = progress),
                          output_sources = info.document_output,
                          output_pdf = info.document_output)
                    }
                  using(database_context.open_database(session_name, output = true))(
                    session_database =>
                      documents.foreach(_.write(session_database.db, session_name)))
                  (documents.flatMap(_.log_lines), Nil)
                }
              }
              else (Nil, Nil)
            }
            catch {
              case exn: Document_Build.Build_Error => (exn.log_lines, exn.log_errors)
              case Exn.Interrupt.ERROR(msg) => (Nil, List(msg))
            }


          /* process result */

          val result1 = {
            val more_output =
              session.synchronized {
                Library.trim_line(stdout.toString) ::
                  session.read_process_output() :::
                  document_output
              }

            result0.output(more_output)
              .error(Library.trim_line(stderr.toString))
              .errors_rc(export_errors ::: document_errors)
          }

          val result2 =
            build_errors match {
              case Exn.Res(build_errs) =>
                val errs = build_errs ::: document_errors
                if (errs.nonEmpty) {
                  result1.error_rc.output(
                    errs.flatMap(s => split_lines(Output.error_message_text(s))) :::
                      errs.map(Protocol.Error_Message_Marker.apply))
                }
                else if (progress.stopped && result1.ok) {
                  result1.copy(rc = Process_Result.RC.interrupt)
                }
                else result1
              case Exn.Exn(Exn.Interrupt()) =>
                if (result1.ok) result1.copy(rc = Process_Result.RC.interrupt)
                else result1
              case Exn.Exn(exn) => throw exn
            }

          val process_result =
            if (result2.ok) result2
            else if (was_timeout) result2.error(Output.error_message_text("Timeout")).timeout_rc
            else if (result2.interrupted) result2.error(Output.error_message_text("Interrupt"))
            else result2

          val store_session =
            store.output_session(session_name, store_heap = process_result.ok && store_heap)

          session.clean_process_output()


          /* output heap */

          val output_shasum =
            store_session.heap match {
              case Some(path) => SHA1.shasum(ML_Heap.write_file_digest(path), session_name)
              case None => SHA1.no_shasum
            }

          val log_lines = process_result.out_lines.filterNot(Protocol_Message.Marker.test)

          val build_log =
            Build_Log.Log_File(session_name, process_result.out_lines, cache = store.cache).
              parse_session_info(
                command_timings = true,
                theory_timings = true,
                ml_statistics = true,
                task_statistics = true)

          // write log file
          if (process_result.ok) {
            File.write_gzip(store.output_log_gz(session_name), terminate_lines(log_lines))
          }
          else File.write(store.output_log(session_name), terminate_lines(log_lines))

          // write database
          def write_info(db: SQL.Database): Unit =
            store.write_session_info(db, session_name, session_sources,
              build_log =
                if (process_result.timeout) build_log.error("Timeout") else build_log,
              build =
                Store.Build_Info(
                  sources = sources_shasum,
                  input_heaps = input_shasum,
                  output_heap = output_shasum,
                  process_result.rc,
                  build_context.build_uuid))

          database_server match {
            case Some(db) => write_info(db)
            case None => using(store.open_database(session_name, output = true))(write_info)
          }

          store.in_heaps_database(
            List(store_session), database_server, server = server, progress = progress)

          // messages
          process_result.err_lines.foreach(progress.echo(_))

          if (process_result.ok) {
            val props = build_log.session_timing
            val threads = Markup.Session_Timing.Threads.unapply(props) getOrElse 1
            val timing = Markup.Timing_Properties.get(props)
            progress.echo(
              "Timing " + session_name + " (" + threads + " threads, " + timing.message_factor + ")",
              verbose = true)
            progress.echo(
              "Finished " + session_name + " (" + process_result.timing.message_resources + ")")
          }
          else {
            progress.echo(
              session_name + " FAILED (see also \"isabelle build_log -H Error " +
              session_name + "\")")
            if (!process_result.interrupted) {
              val tail = info.options.int("process_output_tail")
              val suffix =
                if (tail == 0) log_lines else log_lines.drop(log_lines.length - tail max 0)
              val prefix =
                if (log_lines.length == suffix.length) Nil else List("...")
              progress.echo(Library.trim_line(cat_lines(prefix ::: suffix)))
            }
          }

          Result(process_result.copy(out_lines = log_lines), output_shasum)
        }
      }

    override def cancel(): Unit = future_result.cancel()
    override def is_finished: Boolean = future_result.is_finished
    override def join: Result = future_result.join
  }
}
