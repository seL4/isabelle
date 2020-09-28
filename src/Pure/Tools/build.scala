/*  Title:      Pure/Tools/build.scala
    Author:     Makarius
    Options:    :folding=explicit:

Build and manage Isabelle sessions.
*/

package isabelle


import scala.collection.{SortedSet, mutable}
import scala.annotation.tailrec


object Build
{
  /** auxiliary **/

  /* persistent build info */

  sealed case class Session_Info(
    sources: String,
    input_heaps: List[String],
    output_heap: Option[String],
    return_code: Int)
  {
    def ok: Boolean = return_code == 0
  }


  /* queue with scheduling information */

  private object Queue
  {
    type Timings = (List[Properties.T], Double)

    def load_timings(progress: Progress, store: Sessions.Store, session_name: String): Timings =
    {
      val no_timings: Timings = (Nil, 0.0)

      store.access_database(session_name) match {
        case None => no_timings
        case Some(db) =>
          def ignore_error(msg: String) =
          {
            progress.echo_warning("Ignoring bad database " + db + (if (msg == "") "" else "\n" + msg))
            no_timings
          }
          try {
            val command_timings = store.read_command_timings(db, session_name)
            val session_timing =
              store.read_session_timing(db, session_name) match {
                case Markup.Elapsed(t) => t
                case _ => 0.0
              }
            (command_timings, session_timing)
          }
          catch {
            case ERROR(msg) => ignore_error(msg)
            case exn: java.lang.Error => ignore_error(Exn.message(exn))
            case _: XML.Error => ignore_error("")
          }
          finally { db.close }
      }
    }

    def make_session_timing(sessions_structure: Sessions.Structure, timing: Map[String, Double])
      : Map[String, Double] =
    {
      val maximals = sessions_structure.build_graph.maximals.toSet
      def desc_timing(session_name: String): Double =
      {
        if (maximals.contains(session_name)) timing(session_name)
        else {
          val descendants = sessions_structure.build_descendants(List(session_name)).toSet
          val g = sessions_structure.build_graph.restrict(descendants)
          (0.0 :: g.maximals.flatMap(desc => {
            val ps = g.all_preds(List(desc))
            if (ps.exists(p => !timing.isDefinedAt(p))) None
            else Some(ps.map(timing(_)).sum)
          })).max
        }
      }
      timing.keySet.iterator.map(name => (name -> desc_timing(name))).toMap.withDefaultValue(0.0)
    }

    def apply(progress: Progress, sessions_structure: Sessions.Structure, store: Sessions.Store)
      : Queue =
    {
      val graph = sessions_structure.build_graph
      val names = graph.keys

      val timings = names.map(name => (name, load_timings(progress, store, name)))
      val command_timings =
        timings.map({ case (name, (ts, _)) => (name, ts) }).toMap.withDefaultValue(Nil)
      val session_timing =
        make_session_timing(sessions_structure,
          timings.map({ case (name, (_, t)) => (name, t) }).toMap)

      object Ordering extends scala.math.Ordering[String]
      {
        def compare_timing(name1: String, name2: String): Int =
        {
          val t1 = session_timing(name1)
          val t2 = session_timing(name2)
          if (t1 == 0.0 || t2 == 0.0) 0
          else t1 compare t2
        }

        def compare(name1: String, name2: String): Int =
          compare_timing(name2, name1) match {
            case 0 =>
              sessions_structure(name2).timeout compare sessions_structure(name1).timeout match {
                case 0 => name1 compare name2
                case ord => ord
              }
            case ord => ord
          }
      }

      new Queue(graph, SortedSet(names: _*)(Ordering), command_timings)
    }
  }

  private class Queue(
    graph: Graph[String, Sessions.Info],
    order: SortedSet[String],
    val command_timings: String => List[Properties.T])
  {
    def is_inner(name: String): Boolean = !graph.is_maximal(name)

    def is_empty: Boolean = graph.is_empty

    def - (name: String): Queue =
      new Queue(graph.del_node(name),
        order - name,  // FIXME scala-2.10.0 .. 2.12.4 TreeSet problem!?
        command_timings)

    def dequeue(skip: String => Boolean): Option[(String, Sessions.Info)] =
    {
      val it = order.iterator.dropWhile(name =>
        skip(name)
          || !graph.defined(name)  // FIXME scala-2.10.0 .. 2.12.4 TreeSet problem!?
          || !graph.is_minimal(name))
      if (it.hasNext) { val name = it.next; Some((name, graph.get_node(name))) }
      else None
    }
  }


  /* PIDE protocol handler */

  /* job: running prover process */

  private class Job(progress: Progress,
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

    private val graph_file = Isabelle_System.tmp_file("session_graph", "pdf")
    graphview.Graph_File.write(options, graph_file, deps(session_name).session_graph_display)

    private val export_consumer =
      Export.consumer(store.open_database(session_name, output = true), cache = store.xz_cache)

    private val future_result: Future[Process_Result] =
      Future.thread("build", uninterruptible = true) {
        val parent = info.parent.getOrElse("")
        val base = deps(parent)
        val args_yxml =
          YXML.string_of_body(
            {
              import XML.Encode._
              pair(list(pair(string, int)), pair(list(properties), pair(bool,
                pair(Path.encode, pair(list(pair(Path.encode, Path.encode)), pair(string,
                pair(string, pair(string, pair(string, pair(Path.encode,
                pair(list(pair(Options.encode, list(pair(string, properties)))),
                pair(list(pair(string, properties)),
                pair(list(pair(string, string)),
                pair(list(string), pair(list(pair(string, string)),
                pair(list(string), list(string)))))))))))))))))(
              (Symbol.codes, (command_timings0, (verbose,
                (store.browser_info, (info.document_files, (File.standard_path(graph_file),
                (parent, (info.chapter, (session_name, (Path.current,
                (info.theories,
                (sessions_structure.session_positions,
                (sessions_structure.dest_session_directories,
                (base.doc_names, (base.global_theories.toList,
                (base.loaded_theories.keys, info.bibtex_entries.map(_.info))))))))))))))))))
            })

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

        val resources = new Resources(sessions_structure, deps(parent))
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
                case Markup.Loading_Theory(name) =>
                  progress.theory(Progress.Theory(name, session = session_name))
                  true
                case _ => false
              }

            private def export(msg: Prover.Protocol_Output): Boolean =
              msg.properties match {
                case Protocol.Export(args) =>
                  export_consumer(session_name, args, msg.bytes)
                  true
                case _ => false
              }

            private def command_timing(props: Properties.T): Option[Properties.T] =
              for {
                props1 <- Markup.Command_Timing.unapply(props)
                elapsed <- Markup.Elapsed.unapply(props1)
                elapsed_time = Time.seconds(elapsed)
                if elapsed_time.is_relevant && elapsed_time >= options.seconds("command_timing_threshold")
              } yield props1.filter(p => Markup.command_timing_properties(p._1))

            override val functions =
              List(
                Markup.Build_Session_Finished.name -> build_session_finished,
                Markup.Loading_Theory.name -> loading_theory,
                Markup.EXPORT -> export,
                fun(Markup.Command_Timing.name, command_timings, command_timing),
                fun(Markup.Theory_Timing.name, theory_timings, Markup.Theory_Timing.unapply),
                fun(Markup.Session_Timing.name, session_timings, Markup.Session_Timing.unapply),
                fun(Markup.Task_Statistics.name, task_statistics, Markup.Task_Statistics.unapply))
          })

        session.runtime_statistics += Session.Consumer("ML_statistics")
          {
            case Session.Runtime_Statistics(props) => runtime_statistics += props
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

        val errors =
          Isabelle_Thread.interrupt_handler(_ => process.terminate) {
            Exn.capture { process.await_startup } match {
              case Exn.Res(_) =>
                session.protocol_command("build_session", args_yxml)
                Build_Session_Errors.result
              case Exn.Exn(exn) => Exn.Res(List(Exn.message(exn)))
            }
          }

        val process_result =
          Isabelle_Thread.interrupt_handler(_ => process.terminate) { process.await_shutdown }
        val process_output =
          stdout.toString ::
          messages.toList.map(message =>
            Symbol.encode(Protocol.message_text(List(message), metric = Symbol.Metric))) :::
          command_timings.toList.map(Protocol.Command_Timing_Marker.apply) :::
          theory_timings.toList.map(Protocol.Theory_Timing_Marker.apply) :::
          session_timings.toList.map(Protocol.Session_Timing_Marker.apply) :::
          runtime_statistics.toList.map(Protocol.ML_Statistics_Marker.apply) :::
          task_statistics.toList.map(Protocol.Task_Statistics_Marker.apply)

        val result =
          process_result.output(process_output).error(Library.trim_line(stderr.toString))

        errors match {
          case Exn.Res(Nil) => result
          case Exn.Res(errs) =>
            result.error_rc.output(
              errs.flatMap(s => split_lines(Output.error_message_text(s))) :::
                errs.map(Protocol.Error_Message_Marker.apply))
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
      val result0 = future_result.join
      val result1 =
        export_consumer.shutdown(close = true).map(Output.error_message_text) match {
          case Nil => result0
          case errs => result0.errors(errs).error_rc
        }

      if (result1.ok)
        Present.finish(progress, store.browser_info, graph_file, info, session_name)

      graph_file.delete

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



  /** build with results **/

  class Results private[Build](results: Map[String, (Option[Process_Result], Sessions.Info)])
  {
    def sessions: Set[String] = results.keySet
    def cancelled(name: String): Boolean = results(name)._1.isEmpty
    def apply(name: String): Process_Result = results(name)._1.getOrElse(Process_Result(1))
    def info(name: String): Sessions.Info = results(name)._2
    val rc: Int =
      (0 /: results.iterator.map(
        { case (_, (Some(r), _)) => r.rc case (_, (None, _)) => 1 }))(_ max _)
    def ok: Boolean = rc == 0

    override def toString: String = rc.toString
  }

  def session_finished(session_name: String, process_result: Process_Result): String =
    "Finished " + session_name + " (" + process_result.timing.message_resources + ")"

  def session_timing(session_name: String, build_log: Build_Log.Session_Info): String =
  {
    val props = build_log.session_timing
    val threads = Markup.Session_Timing.Threads.unapply(props) getOrElse 1
    val timing = Markup.Timing_Properties.parse(props)
    "Timing " + session_name + " (" + threads + " threads, " + timing.message_factor + ")"
  }

  def build(
    options: Options,
    selection: Sessions.Selection = Sessions.Selection.empty,
    progress: Progress = new Progress,
    check_unknown_files: Boolean = false,
    build_heap: Boolean = false,
    clean_build: Boolean = false,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    infos: List[Sessions.Info] = Nil,
    numa_shuffling: Boolean = false,
    max_jobs: Int = 1,
    list_files: Boolean = false,
    check_keywords: Set[String] = Set.empty,
    fresh_build: Boolean = false,
    no_build: Boolean = false,
    soft_build: Boolean = false,
    verbose: Boolean = false,
    export_files: Boolean = false): Results =
  {
    val build_options =
      options +
        "completion_limit=0" +
        "editor_tracing_messages=0" +
        "pide_reports=false"

    val store = Sessions.store(build_options)

    Isabelle_Fonts.init()


    /* session selection and dependencies */

    val full_sessions =
      Sessions.load_structure(build_options, dirs = dirs, select_dirs = select_dirs, infos = infos)

    def sources_stamp(deps: Sessions.Deps, session_name: String): String =
    {
      val digests =
        full_sessions(session_name).meta_digest ::
        deps.sources(session_name) :::
        deps.imported_sources(session_name)
      SHA1.digest(cat_lines(digests.map(_.toString).sorted)).toString
    }

    val deps =
    {
      val deps0 =
        Sessions.deps(full_sessions.selection(selection),
          progress = progress, inlined_files = true, verbose = verbose,
          list_files = list_files, check_keywords = check_keywords).check_errors

      if (soft_build && !fresh_build) {
        val outdated =
          deps0.sessions_structure.build_topological_order.flatMap(name =>
            store.access_database(name) match {
              case Some(db) =>
                using(db)(store.read_build(_, name)) match {
                  case Some(build)
                  if build.ok && build.sources == sources_stamp(deps0, name) => None
                  case _ => Some(name)
                }
              case None => Some(name)
            })

        Sessions.deps(full_sessions.selection(Sessions.Selection(sessions = outdated)),
          progress = progress, inlined_files = true).check_errors
      }
      else deps0
    }


    /* check unknown files */

    if (check_unknown_files) {
      val source_files =
        (for {
          (_, base) <- deps.session_bases.iterator
          (path, _) <- base.sources.iterator
        } yield path).toList
      val exclude_files = List(Path.explode("$POLYML_EXE")).map(_.canonical_file)
      val unknown_files =
        Mercurial.check_files(source_files)._2.
          filterNot(path => exclude_files.contains(path.canonical_file))
      if (unknown_files.nonEmpty) {
        progress.echo_warning("Unknown files (not part of the underlying Mercurial repository):" +
          unknown_files.map(path => path.expand.implode).sorted.mkString("\n  ", "\n  ", ""))
      }
    }


    /* main build process */

    val queue = Queue(progress, deps.sessions_structure, store)

    store.prepare_output_dir()

    if (clean_build) {
      for (name <- full_sessions.imports_descendants(full_sessions.imports_selection(selection))) {
        val (relevant, ok) = store.clean_output(name)
        if (relevant) {
          if (ok) progress.echo("Cleaned " + name)
          else progress.echo(name + " FAILED to clean")
        }
      }
    }

    // scheduler loop
    case class Result(
      current: Boolean,
      heap_digest: Option[String],
      process: Option[Process_Result],
      info: Sessions.Info)
    {
      def ok: Boolean =
        process match {
          case None => false
          case Some(res) => res.rc == 0
        }
    }

    def sleep()
    {
      Isabelle_Thread.interrupt_handler(_ => progress.stop) { Time.seconds(0.5).sleep }
    }

    val numa_nodes = new NUMA.Nodes(numa_shuffling)

    @tailrec def loop(
      pending: Queue,
      running: Map[String, (List[String], Job)],
      results: Map[String, Result]): Map[String, Result] =
    {
      def used_node(i: Int): Boolean =
        running.iterator.exists(
          { case (_, (_, job)) => job.numa_node.isDefined && job.numa_node.get == i })

      if (pending.is_empty) results
      else {
        if (progress.stopped) {
          for ((_, (_, job)) <- running) job.terminate
        }

        running.find({ case (_, (_, job)) => job.is_finished }) match {
          case Some((session_name, (input_heaps, job))) =>
            //{{{ finish job

            val (process_result, heap_digest) = job.join

            val log_lines = process_result.out_lines.filterNot(Protocol_Message.Marker.test)
            val process_result_tail =
            {
              val tail = job.info.options.int("process_output_tail")
              process_result.copy(
                out_lines =
                  "(see also " + store.output_log(session_name).file.toString + ")" ::
                  (if (tail == 0) log_lines else log_lines.drop(log_lines.length - tail max 0)))
            }

            val build_log =
              Build_Log.Log_File(session_name, process_result.out_lines).
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
            using(store.open_database(session_name, output = true))(db =>
              store.write_session_info(db, session_name,
                build_log =
                  if (process_result.timeout) build_log.error("Timeout") else build_log,
                build =
                  Session_Info(sources_stamp(deps, session_name), input_heaps, heap_digest,
                    process_result.rc)))

            // messages
            process_result.err_lines.foreach(progress.echo)

            if (process_result.ok) {
              if (verbose) progress.echo(session_timing(session_name, build_log))
              progress.echo(session_finished(session_name, process_result))
            }
            else {
              progress.echo(session_name + " FAILED")
              if (!process_result.interrupted) progress.echo(process_result_tail.out)
            }

            loop(pending - session_name, running - session_name,
              results +
                (session_name -> Result(false, heap_digest, Some(process_result_tail), job.info)))
            //}}}
          case None if running.size < (max_jobs max 1) =>
            //{{{ check/start next job
            pending.dequeue(running.isDefinedAt) match {
              case Some((session_name, info)) =>
                val ancestor_results =
                  deps.sessions_structure.build_requirements(List(session_name)).
                    filterNot(_ == session_name).map(results(_))
                val ancestor_heaps = ancestor_results.flatMap(_.heap_digest)

                val do_store =
                  build_heap || Sessions.is_pure(session_name) || queue.is_inner(session_name)

                val (current, heap_digest) =
                {
                  store.access_database(session_name) match {
                    case Some(db) =>
                      using(db)(store.read_build(_, session_name)) match {
                        case Some(build) =>
                          val heap_digest = store.find_heap_digest(session_name)
                          val current =
                            !fresh_build &&
                            build.ok &&
                            build.sources == sources_stamp(deps, session_name) &&
                            build.input_heaps == ancestor_heaps &&
                            build.output_heap == heap_digest &&
                            !(do_store && heap_digest.isEmpty)
                          (current, heap_digest)
                        case None => (false, None)
                      }
                    case None => (false, None)
                  }
                }
                val all_current = current && ancestor_results.forall(_.current)

                if (all_current)
                  loop(pending - session_name, running,
                    results +
                      (session_name -> Result(true, heap_digest, Some(Process_Result(0)), info)))
                else if (no_build) {
                  progress.echo_if(verbose, "Skipping " + session_name + " ...")
                  loop(pending - session_name, running,
                    results +
                      (session_name -> Result(false, heap_digest, Some(Process_Result(1)), info)))
                }
                else if (ancestor_results.forall(_.ok) && !progress.stopped) {
                  progress.echo((if (do_store) "Building " else "Running ") + session_name + " ...")

                  store.clean_output(session_name)
                  using(store.open_database(session_name, output = true))(
                    store.init_session_info(_, session_name))

                  val numa_node = numa_nodes.next(used_node)
                  val job =
                    new Job(progress, session_name, info, deps, store, do_store, verbose,
                      numa_node, queue.command_timings(session_name))
                  loop(pending, running + (session_name -> (ancestor_heaps, job)), results)
                }
                else {
                  progress.echo(session_name + " CANCELLED")
                  loop(pending - session_name, running,
                    results + (session_name -> Result(false, heap_digest, None, info)))
                }
              case None => sleep(); loop(pending, running, results)
            }
            ///}}}
          case None => sleep(); loop(pending, running, results)
        }
      }
    }


    /* build results */

    val results0 =
      if (deps.is_empty) {
        progress.echo_warning("Nothing to build")
        Map.empty[String, Result]
      }
      else Isabelle_Thread.uninterruptible { loop(queue, Map.empty, Map.empty) }

    val results =
      new Results(
        (for ((name, result) <- results0.iterator)
          yield (name, (result.process, result.info))).toMap)

    if (export_files) {
      for (name <- full_sessions.imports_selection(selection).iterator if results(name).ok) {
        val info = results.info(name)
        if (info.export_files.nonEmpty) {
          progress.echo("Exporting " + info.name + " ...")
          for ((dir, prune, pats) <- info.export_files) {
            Export.export_files(store, name, info.dir + dir,
              progress = if (verbose) progress else new Progress,
              export_prune = prune,
              export_patterns = pats)
          }
        }
      }
    }

    if (results.rc != 0 && (verbose || !no_build)) {
      val unfinished =
        (for {
          name <- results.sessions.iterator
          if !results(name).ok
         } yield name).toList.sorted
      progress.echo("Unfinished session(s): " + commas(unfinished))
    }


    /* global browser info */

    if (!no_build) {
      val browser_chapters =
        (for {
          (name, result) <- results0.iterator
          if result.ok
          info = full_sessions(name)
          if info.options.bool("browser_info")
        } yield (info.chapter, (name, info.description))).toList.groupBy(_._1).
            map({ case (chapter, es) => (chapter, es.map(_._2)) }).filterNot(_._2.isEmpty)

      for ((chapter, entries) <- browser_chapters)
        Present.update_chapter_index(store.browser_info, chapter, entries)

      if (browser_chapters.nonEmpty) Present.make_global_index(store.browser_info)
    }

    results
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("build", "build and manage Isabelle sessions", args =>
  {
    val build_options = Word.explode(Isabelle_System.getenv("ISABELLE_BUILD_OPTIONS"))

    var base_sessions: List[String] = Nil
    var select_dirs: List[Path] = Nil
    var numa_shuffling = false
    var requirements = false
    var soft_build = false
    var exclude_session_groups: List[String] = Nil
    var all_sessions = false
    var build_heap = false
    var clean_build = false
    var dirs: List[Path] = Nil
    var export_files = false
    var fresh_build = false
    var session_groups: List[String] = Nil
    var max_jobs = 1
    var check_keywords: Set[String] = Set.empty
    var list_files = false
    var no_build = false
    var options = Options.init(opts = build_options)
    var verbose = false
    var exclude_sessions: List[String] = Nil

    val getopts = Getopts("""
Usage: isabelle build [OPTIONS] [SESSIONS ...]

  Options are:
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -N           cyclic shuffling of NUMA CPU nodes (performance tuning)
    -R           refer to requirements of selected sessions
    -S           soft build: only observe changes of sources, not heap images
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -b           build heap images
    -c           clean build
    -d DIR       include session directory
    -e           export files from session specification into file-system
    -f           fresh build
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs (default 1)
    -k KEYWORD   check theory sources for conflicts with proposed keywords
    -l           list session source files
    -n           no build -- test dependencies only
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Build and manage Isabelle sessions, depending on implicit settings:

""" + Library.prefix_lines("  ",  Build_Log.Settings.show()) + "\n",
      "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
      "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
      "N" -> (_ => numa_shuffling = true),
      "R" -> (_ => requirements = true),
      "S" -> (_ => soft_build = true),
      "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
      "a" -> (_ => all_sessions = true),
      "b" -> (_ => build_heap = true),
      "c" -> (_ => clean_build = true),
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "e" -> (_ => export_files = true),
      "f" -> (_ => fresh_build = true),
      "g:" -> (arg => session_groups = session_groups ::: List(arg)),
      "j:" -> (arg => max_jobs = Value.Int.parse(arg)),
      "k:" -> (arg => check_keywords = check_keywords + arg),
      "l" -> (_ => list_files = true),
      "n" -> (_ => no_build = true),
      "o:" -> (arg => options = options + arg),
      "v" -> (_ => verbose = true),
      "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

    val sessions = getopts(args)

    val progress = new Console_Progress(verbose = verbose)

    val start_date = Date.now()

    if (verbose) {
      progress.echo(
        "Started at " + Build_Log.print_date(start_date) +
          " (" + Isabelle_System.getenv("ML_IDENTIFIER") + " on " + Isabelle_System.hostname() +")")
      progress.echo(Build_Log.Settings.show() + "\n")
    }

    val results =
      progress.interrupt_handler {
        build(options,
          selection = Sessions.Selection(
            requirements = requirements,
            all_sessions = all_sessions,
            base_sessions = base_sessions,
            exclude_session_groups = exclude_session_groups,
            exclude_sessions = exclude_sessions,
            session_groups = session_groups,
            sessions = sessions),
          progress = progress,
          check_unknown_files = Mercurial.is_repository(Path.explode("~~")),
          build_heap = build_heap,
          clean_build = clean_build,
          dirs = dirs,
          select_dirs = select_dirs,
          numa_shuffling = NUMA.enabled_warning(progress, numa_shuffling),
          max_jobs = max_jobs,
          list_files = list_files,
          check_keywords = check_keywords,
          fresh_build = fresh_build,
          no_build = no_build,
          soft_build = soft_build,
          verbose = verbose,
          export_files = export_files)
      }
    val end_date = Date.now()
    val elapsed_time = end_date.time - start_date.time

    if (verbose) {
      progress.echo("\nFinished at " + Build_Log.print_date(end_date))
    }

    val total_timing =
      (Timing.zero /: results.sessions.iterator.map(a => results(a).timing))(_ + _).
        copy(elapsed = elapsed_time)
    progress.echo(total_timing.message_resources)

    sys.exit(results.rc)
  })


  /* build logic image */

  def build_logic(options: Options, logic: String,
    progress: Progress = new Progress,
    build_heap: Boolean = false,
    dirs: List[Path] = Nil,
    fresh: Boolean = false,
    strict: Boolean = false): Int =
  {
    val selection = Sessions.Selection.session(logic)
    val rc =
      if (!fresh && build(options, selection = selection,
            build_heap = build_heap, no_build = true, dirs = dirs).ok) 0
      else {
        progress.echo("Build started for Isabelle/" + logic + " ...")
        Build.build(options, selection = selection, progress = progress,
          build_heap = build_heap, fresh_build = fresh, dirs = dirs).rc
      }
    if (strict && rc != 0) error("Failed to build Isabelle/" + logic) else rc
  }
}
