/*  Title:      Pure/System/benchmark.scala
    Author:     Fabian Huch, TU Muenchen

Host platform benchmarks for performance estimation.
*/

package isabelle


object Benchmark {
  /* ZF-Constructible as representative benchmark session with short build time and requirements */

  val benchmark_session = "ZF-Constructible"

  def benchmark_command(
    host: Build_Cluster.Host,
    ssh: SSH.System = SSH.Local,
    isabelle_home: Path = Path.current,
  ): String = {
    val options = Options.Spec.eq("build_hostname", host.name) :: host.options
    ssh.bash_path(isabelle_home + Path.explode("bin/isabelle")) + " benchmark" +
      Options.Spec.bash_strings(options, bg = true)
  }

  def benchmark_requirements(options: Options, progress: Progress = new Progress()): Unit = {
    val res =
      Build.build(
        options.string("build_engine") = Build.Default_Engine().name,
        selection = Sessions.Selection(requirements = true, sessions = List(benchmark_session)),
        progress = progress, build_heap = true)
    if (!res.ok) error("Failed building requirements")
  }

  def benchmark(options: Options, progress: Progress = new Progress()): Unit = {
    val hostname = options.string("build_hostname")
    val store = Store(options)

    using(store.open_server()) { server =>
      using_optional(store.maybe_open_database_server(server = server)) { database_server =>
        val db = store.open_build_database(path = Host.private_data.database, server = server)

        progress.echo("Starting benchmark ...")
        val selection = Sessions.Selection(sessions = List(benchmark_session))
        val full_sessions = Sessions.load_structure(options.int("threads") = 1)

        val build_context =
          Build.Context(store, new Build.Default_Engine,
            Sessions.deps(full_sessions.selection(selection)).check_errors)

        val sessions = Build_Process.Sessions.empty.init(build_context, database_server, progress)
        val session = sessions(benchmark_session)

        val heaps = session.ancestors.map(store.output_heap)
        ML_Heap.restore(database_server, heaps, cache = store.cache.compress)

        val local_options =
          options
            .bool.update("build_database_server", false)
            .bool.update("build_database", false)

        benchmark_requirements(local_options, progress)
        ML_Heap.restore(database_server, heaps, cache = store.cache.compress)

        def get_shasum(session_name: String): SHA1.Shasum = {
          val ancestor_shasums = sessions(session_name).ancestors.map(get_shasum)

          val input_shasum =
            if (ancestor_shasums.isEmpty) ML_Process.bootstrap_shasum()
            else SHA1.flat_shasum(ancestor_shasums)

          store.check_output(
            database_server, session_name,
            session_options = build_context.sessions_structure(session_name).options,
            sources_shasum = sessions(session_name).sources_shasum,
            input_shasum = input_shasum,
            fresh_build = false,
            store_heap = false)._2
        }

        val deps = Sessions.deps(full_sessions.selection(selection)).check_errors
        val background = deps.background(benchmark_session)
        val input_shasum = get_shasum(benchmark_session)
        val node_info = Host.Node_Info(hostname, None, Nil)

        val local_build_context = build_context.copy(store = Store(local_options))

        val build =
          Build_Job.start_session(local_build_context, session, progress, No_Logger, server,
            background, session.sources_shasum, input_shasum, node_info, false)

        val timing =
          build.join match {
            case Some(result) if result.process_result.ok => result.process_result.timing
            case _ => error("Failed to build benchmark session")
          }

        val score = Time.seconds(1000).ms.toDouble / (1 + timing.elapsed.ms)
        progress.echo(
          "Finished benchmark in " + timing.message + ". Score: " + String.format("%.2f", score))

        Host.write_info(db, Host.Info.init(hostname = hostname, score = Some(score)))
      }
    }
  }

  val isabelle_tool = Isabelle_Tool("benchmark", "run system benchmark",
    Scala_Project.here,
    { args =>
      var options = Options.init()

      val getopts = Getopts("""
Usage: isabelle benchmark [OPTIONS]

  Options are:
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Run a system benchmark.
""",
        "o:" -> (arg => options = options + arg))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      benchmark(options, progress = progress)
    })
}