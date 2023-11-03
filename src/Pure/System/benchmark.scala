/*  Title:      Pure/System/benchmark.scala
    Author:     Fabian Huch, TU Muenchen

Host platform benchmarks for performance estimation.
*/

package isabelle


object Benchmark {

  def benchmark_command(
    host: Build_Cluster.Host,
    ssh: SSH.System = SSH.Local,
    isabelle_home: Path = Path.current,
  ): String = {
    val options = Options.Spec("build_hostname", Some(host.name)) :: host.options
    ssh.bash_path(isabelle_home + Path.explode("bin/isabelle")) + " benchmark" +
      options.map(opt => " -o " + Bash.string(opt.print)).mkString
  }

  def benchmark(options: Options, progress: Progress = new Progress()): Unit = {
    val hostname = options.string("build_hostname")
    val store = Store(options)

    using(store.open_server()) { server =>
      val db = store.open_build_database(path = Host.private_data.database, server = server)

      progress.echo("Starting benchmark...")
      val start = Time.now()

      // TODO proper benchmark
      def fib(n: Long): Long = if (n < 2) 1 else fib(n - 2) + fib(n - 1)
      val result = fib(42)

      val stop = Time.now()
      val timing = stop - start

      val score = Time.seconds(100).ms.toDouble / (1 + timing.ms)
      progress.echo(
        "Finished benchmark in " + timing.message + ". Score: " + String.format("%.2f", score))

      Host.write_info(db, Host.Info.gather(hostname, score = Some(score)))
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