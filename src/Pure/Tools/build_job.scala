/*  Title:      Pure/Tools/build_job.scala
    Author:     Makarius

Build job running prover process, with rudimentary PIDE session.
*/

package isabelle


import scala.collection.mutable


class Build_Job(progress: Progress,
  session_name: String,
  val info: Sessions.Info,
  deps: Sessions.Deps,
  store: Sessions.Store,
  do_store: Boolean,
  verbose: Boolean,
  val numa_node: Option[Int],
  command_timings0: List[Properties.T])
{
  val options: Options = NUMA.policy_options(info.options, numa_node)

  private val sessions_structure = deps.sessions_structure

  private val future_result: Future[Process_Result] =
    Future.thread("build", uninterruptible = true) {
      val parent = info.parent.getOrElse("")
      val base = deps(parent)

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

      val resources = new Resources(sessions_structure, base, command_timings = command_timings0)
      val session =
        new Session(options, resources) {
          override val xml_cache: XML.Cache = store.xml_cache
          override val xz_cache: XZ.Cache = store.xz_cache
        }

      object Build_Session_Errors
      {
        private val promise: Promise[List[String]] = Future.promise

        def result: Exn.Result[List[String]] = promise.join_result
        def cancel: Unit = promise.cancel
        def apply(errs: List[String])
        {
          try { promise.fulfill(errs) }
          catch { case _: IllegalStateException => }
        }
      }

      val export_consumer =
        Export.consumer(store.open_database(session_name, output = true), cache = store.xz_cache)

      val stdout = new StringBuilder(1000)
      val stderr = new StringBuilder(1000)
      val messages = new mutable.ListBuffer[XML.Elem]
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
          override def exit() { Build_Session_Errors.cancel }

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
                export_consumer(session_name, args, msg.bytes)
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

      session.finished_theories += Session.Consumer[Command.State]("finished_theories")
        {
          case st =>
            val command = st.command
            val theory_name = command.node_name.theory
            val args = Protocol.Export.Args(theory_name = theory_name, name = Export.MARKUP)
            val xml =
              st.markups(Command.Markup_Index.markup)
                .to_XML(command.range, command.source, Markup.Elements.full)
            export_consumer(session_name, args, Bytes(YXML.string_of_body(xml)))
        }

      session.all_messages += Session.Consumer[Any]("build_session_output")
        {
          case msg: Prover.Output =>
            val message = msg.message
            if (msg.is_stdout) {
              stdout ++= Symbol.encode(XML.content(message))
            }
            else if (msg.is_stderr) {
              stderr ++= Symbol.encode(XML.content(message))
            }
            else if (Protocol.is_exported(message)) {
              messages += message
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

      val eval_main = Command_Line.ML_tool("Isabelle_Process.init_build ()" :: eval_store)

      val process =
        Isabelle_Process(session, options, sessions_structure, store,
          logic = parent, raw_ml_system = is_pure,
          use_prelude = use_prelude, eval_main = eval_main,
          cwd = info.dir.file, env = env)

      val build_errors =
        Isabelle_Thread.interrupt_handler(_ => process.terminate) {
          Exn.capture { process.await_startup } match {
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
        Isabelle_Thread.interrupt_handler(_ => process.terminate) { process.await_shutdown }

      session.stop()

      val export_errors =
        export_consumer.shutdown(close = true).map(Output.error_message_text)

      val (document_output, document_errors) =
        try {
          if (build_errors.isInstanceOf[Exn.Res[_]] && process_result.ok && info.documents.nonEmpty)
          {
            using(store.open_database_context(deps.sessions_structure))(db_context =>
              {
                val documents =
                  Presentation.build_documents(session_name, deps, db_context,
                    output_sources = info.document_output,
                    output_pdf = info.document_output,
                    progress = progress,
                    verbose = verbose)
                db_context.output_database(session_name)(db =>
                  documents.foreach(_.write(db, session_name)))
                (documents.flatMap(_.log_lines), Nil)
              })
          }
          (Nil, Nil)
        }
        catch { case Exn.Interrupt.ERROR(msg) => (Nil, List(msg)) }

      val result =
      {
        val more_output =
          Library.trim_line(stdout.toString) ::
            messages.toList.map(message =>
              Symbol.encode(Protocol.message_text(List(message), metric = Symbol.Metric))) :::
            command_timings.toList.map(Protocol.Command_Timing_Marker.apply) :::
            theory_timings.toList.map(Protocol.Theory_Timing_Marker.apply) :::
            session_timings.toList.map(Protocol.Session_Timing_Marker.apply) :::
            runtime_statistics.toList.map(Protocol.ML_Statistics_Marker.apply) :::
            task_statistics.toList.map(Protocol.Task_Statistics_Marker.apply) :::
            document_output

        val more_errors =
          Library.trim_line(stderr.toString) :: export_errors ::: document_errors

        process_result.output(more_output).errors(more_errors)
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

  def terminate: Unit = future_result.cancel
  def is_finished: Boolean = future_result.is_finished

  private val timeout_request: Option[Event_Timer.Request] =
  {
    if (info.timeout > Time.zero)
      Some(Event_Timer.request(Time.now() + info.timeout) { terminate })
    else None
  }

  def join: (Process_Result, Option[String]) =
  {
    val result1 = future_result.join

    val was_timeout =
      timeout_request match {
        case None => false
        case Some(request) => !request.cancel
      }

    val result2 =
      if (result1.interrupted) {
        if (was_timeout) result1.error(Output.error_message_text("Timeout")).was_timeout
        else result1.error(Output.error_message_text("Interrupt"))
      }
      else result1

    val heap_digest =
      if (result2.ok && do_store && store.output_heap(session_name).is_file)
        Some(Sessions.write_heap_digest(store.output_heap(session_name)))
      else None

    (result2, heap_digest)
  }
}
