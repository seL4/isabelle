/*  Title:      Pure/Build/build_benchmark.scala
    Author:     Fabian Huch, TU Muenchen

Host platform benchmarks for performance estimation.
*/

package isabelle


import scala.collection.mutable


object Build_Benchmark {
  /* benchmark */

  def benchmark_session(options: Options) = options.string("build_benchmark_session")

  def benchmark_command(
    options: Options,
    host: Build_Cluster.Host,
    ssh: SSH.System = SSH.Local,
    isabelle_home: Path = Path.current,
  ): String = {
    val benchmark_options =
      List(
        Options.Spec.eq("build_hostname", host.name),
        Options.Spec("build_database_server"),
        options.spec("build_benchmark_session"))
    ssh.bash_path(Isabelle_Tool.exe(isabelle_home)) + " build_benchmark" +
      Options.Spec.bash_strings(benchmark_options ::: host.options, bg = true)
  }

  def benchmark_requirements(options: Options, progress: Progress = new Progress): Unit = {
    val options1 = options.string.update("build_engine", Build.Engine.Default.name)
    val selection =
      Sessions.Selection(requirements = true, sessions = List(benchmark_session(options)))
    Build.build(options1, selection = selection, progress = progress, build_heap = true).check
  }

  def run_benchmark(options: Options, progress: Progress = new Progress): Unit = {
    val hostname = options.string("build_hostname")
    val store = Store(options)

    using(store.open_server()) { server =>
      using_optional(store.maybe_open_database_server(server = server)) { database_server =>
        val db = store.open_build_database(path = Host.private_data.database, server = server)

        progress.echo("Starting benchmark ...")
        val benchmark_session_name = benchmark_session(options)
        val selection = Sessions.Selection(sessions = List(benchmark_session_name))
        val full_sessions = Sessions.load_structure(options + "threads=1")

        val build_deps = Sessions.deps(full_sessions.selection(selection)).check_errors
        val build_context = Build.Context(store, build_deps, jobs = 1)

        val sessions = Build_Process.Sessions.empty.init(build_context, database_server, progress)
        val session = sessions(benchmark_session_name)

        val hierarchy = session.ancestors.map(store.output_session(_, store_heap = true))
        for (heap_db <- database_server) {
          ML_Heap.restore(heap_db, hierarchy, cache = store.cache.compress)
        }

        val local_options = options + "build_database_server=false" + "build_database=false"

        benchmark_requirements(local_options, progress)
        for (heap_db <- database_server) {
          ML_Heap.restore(heap_db, hierarchy, cache = store.cache.compress)
        }

        def get_shasum(name: String): SHA1.Shasum =
          store.check_output(name,
            opened_db = database_server,
            sources_shasum = sessions(name).sources_shasum,
            input_shasum = store.make_shasum(sessions(name).ancestors.map(get_shasum))
          ).output_shasum

        val deps = Sessions.deps(full_sessions.selection(selection)).check_errors
        val background = deps.background(benchmark_session_name)
        val input_shasum = get_shasum(benchmark_session_name)
        val node_info = Host.Node_Info(hostname, None, Nil)

        val local_build_context = build_context.copy(store = Store(local_options))

        val result =
          Build_Job.start_session(local_build_context, session, progress, new Logger, server,
            background, session.sources_shasum, input_shasum, node_info, false).join

        val timing =
          if (result.process_result.ok) result.process_result.timing
          else error("Failed to build benchmark session")

        val score = Time.seconds(1000).ms.toDouble / (1 + timing.elapsed.ms)
        progress.echo(
          "Finished benchmark in " + timing.message + ". Score: " + String.format("%.2f", score))

        Host.write_info(db, Host.Info.init(hostname = hostname, score = Some(score)))
      }
    }
  }

  def benchmark(
    options: Options,
    build_hosts: List[Build_Cluster.Host] = Nil,
    progress: Progress = new Progress
  ): Unit =
    if (build_hosts.isEmpty) run_benchmark(options, progress)
    else {
      val engine = Build.Engine.Default
      val store = engine.build_store(options, build_cluster = true)

      benchmark_requirements(store.options, progress)

      val deps0 = Sessions.deps(Sessions.load_structure(options))
      val build_context = Build.Context(store, deps0, build_hosts = build_hosts)

      val build_cluster = Build_Cluster.make(build_context, progress).open().init().benchmark()
      if (!build_cluster.ok) error("Benchmarking failed")
      build_cluster.stop()

      using(store.open_server()) { server =>
        val db = store.open_build_database(path = Host.private_data.database, server = server)
        for (build_host <- build_hosts) {
          val score =
            (for {
              info <- Host.read_info(db, build_host.name)
              score <- info.benchmark_score
            } yield score).getOrElse(error("No score for host " + quote(build_host.name)))

          progress.echo(build_host.name + ": " + score)
        }
      }
    }

  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("build_benchmark", "run benchmark for build process",
    Scala_Project.here,
    { args =>
      val build_hosts = new mutable.ListBuffer[Build_Cluster.Host]
      var options = Options.init()

      val getopts = Getopts("""
Usage: isabelle build_benchmark [OPTIONS]

  Options are:
    -H HOSTS     additional cluster host specifications of the form
                 NAMES:PARAMETERS (separated by commas)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Run benchmark for build process.
""",
        "H:" -> (arg => build_hosts ++= Build_Cluster.Host.parse(Registry.global, arg)),
        "o:" -> (arg => options = options + arg))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      benchmark(options, build_hosts = build_hosts.toList, progress = progress)
    })
}