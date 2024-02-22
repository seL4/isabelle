/*  Title:      Pure/System/build_benchmark.scala
    Author:     Fabian Huch, TU Muenchen

Host platform benchmarks for performance estimation.
*/

package isabelle


object Build_Benchmark {
  /* benchmark */

  // ZF-Constructible as representative benchmark session with
  // short build time and requirements
  val benchmark_session = "ZF-Constructible"

  def benchmark_command(
    host: Build_Cluster.Host,
    ssh: SSH.System = SSH.Local,
    isabelle_home: Path = Path.current,
  ): String = {
    val options = Options.Spec.eq("build_hostname", host.name) :: host.options
    ssh.bash_path(Isabelle_Tool.exe(isabelle_home)) + " build_benchmark" +
      Options.Spec.bash_strings(options, bg = true)
  }

  def benchmark_requirements(options: Options, progress: Progress = new Progress): Unit = {
    val res =
      Build.build(
        options.string.update("build_engine", Build.Engine.Default.name),
        selection = Sessions.Selection(requirements = true, sessions = List(benchmark_session)),
        progress = progress, build_heap = true)
    if (!res.ok) error("Failed building requirements")
  }

  def benchmark(options: Options, progress: Progress = new Progress): Unit = {
    val hostname = options.string("build_hostname")
    val store = Store(options)

    using(store.open_server()) { server =>
      using_optional(store.maybe_open_database_server(server = server)) { database_server =>
        val db = store.open_build_database(path = Host.private_data.database, server = server)

        progress.echo("Starting benchmark ...")
        val selection = Sessions.Selection(sessions = List(benchmark_session))
        val full_sessions = Sessions.load_structure(options + "threads=1")

        val build_deps = Sessions.deps(full_sessions.selection(selection)).check_errors
        val build_context = Build.Context(store, build_deps, jobs = 1)

        val sessions = Build_Process.Sessions.empty.init(build_context, database_server, progress)
        val session = sessions(benchmark_session)

        val hierachy = session.ancestors.map(store.output_session(_, store_heap = true))
        for (db <- database_server) ML_Heap.restore(db, hierachy, cache = store.cache.compress)

        val local_options = options + "build_database_server=false" + "build_database=false"

        benchmark_requirements(local_options, progress)
        for (db <- database_server) ML_Heap.restore(db, hierachy, cache = store.cache.compress)

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


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("build_benchmark", "run benchmark for build process",
    Scala_Project.here,
    { args =>
      var options = Options.init()

      val getopts = Getopts("""
Usage: isabelle build_benchmark [OPTIONS]

  Options are:
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Run benchmark for build process.
""",
        "o:" -> (arg => options = options + arg))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      benchmark(options, progress = progress)
    })
}