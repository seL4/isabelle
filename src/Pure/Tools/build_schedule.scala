/*  Title:      Pure/Tools/build_schedule.scala
    Author:     Fabian Huch, TU Muenchen

Build schedule generated by Heuristic methods, allowing for more efficient builds.
 */
package isabelle


import Host.Node_Info
import scala.annotation.tailrec


object Build_Schedule {
  /* organized historic timing information (extracted from build logs) */

  case class Timing_Entry(job_name: String, hostname: String, threads: Int, timing: Timing) {
    def elapsed: Time = timing.elapsed
    def proper_cpu: Option[Time] = timing.cpu.proper_ms.map(Time.ms)
  }
  case class Timing_Entries(entries: List[Timing_Entry]) {
    require(entries.nonEmpty)

    def is_empty = entries.isEmpty
    def size = entries.length

    lazy val by_job = entries.groupBy(_.job_name).view.mapValues(Timing_Entries(_)).toMap
    lazy val by_threads = entries.groupBy(_.threads).view.mapValues(Timing_Entries(_)).toMap
    lazy val by_hostname = entries.groupBy(_.hostname).view.mapValues(Timing_Entries(_)).toMap

    def mean_time: Time = Timing_Data.mean_time(entries.map(_.elapsed))
    def best_entry: Timing_Entry = entries.minBy(_.elapsed.ms)
  }

  class Timing_Data private(data: Timing_Entries, val host_infos: Host_Infos) {
    private def inflection_point(last_mono: Int, next: Int): Int =
      last_mono + ((next - last_mono) / 2)

    def best_threads(job_name: String, max_threads: Int): Int = {
      val worse_threads =
        data.by_job.get(job_name).toList.flatMap(_.by_hostname).flatMap {
          case (hostname, data) =>
            val best_threads = data.best_entry.threads
            data.by_threads.keys.toList.sorted.find(_ > best_threads).map(
              inflection_point(best_threads, _))
        }
      (max_threads :: worse_threads).min
    }

    private def hostname_factor(from: String, to: String): Double =
      host_infos.host_factor(host_infos.the_host(from), host_infos.the_host(to))

    private def approximate_threads(entries_unsorted: List[(Int, Time)], threads: Int): Time = {
      val entries = entries_unsorted.sortBy(_._1)

      def sorted_prefix[A](xs: List[A], f: A => Long): List[A] =
        xs match {
          case x1 :: x2 :: xs =>
            if (f(x1) <= f(x2)) x1 :: sorted_prefix(x2 :: xs, f) else x1 :: Nil
          case xs => xs
        }

      def linear(p0: (Int, Time), p1: (Int, Time)): Time = {
        val a = (p1._2 - p0._2).scale(1.0 / (p1._1 - p0._1))
        val b = p0._2 - a.scale(p0._1)
        Time.ms((a.scale(threads) + b).ms max 0)
      }

      val mono_prefix = sorted_prefix(entries, e => -e._2.ms)

      val is_mono = entries == mono_prefix
      val in_prefix = mono_prefix.length > 1 && threads <= mono_prefix.last._1
      val in_inflection =
        !is_mono && mono_prefix.length > 1 && threads < entries.drop(mono_prefix.length).head._1
      if (is_mono || in_prefix || in_inflection) {
        // Model with Amdahl's law
        val t_p =
          Timing_Data.median_time(for {
            (n, t0) <- mono_prefix
            (m, t1) <- mono_prefix
            if m != n
          } yield (t0 - t1).scale(n.toDouble * m / (m - n)))
        val t_c =
          Timing_Data.median_time(for ((n, t) <- mono_prefix) yield t - t_p.scale(1.0 / n))

        def model(threads: Int): Time = Time.ms((t_c + t_p.scale(1.0 / threads)).ms max 0)

        if (is_mono || in_prefix) model(threads)
        else {
          val post_inflection = entries.drop(mono_prefix.length).head
          val inflection_threads = inflection_point(mono_prefix.last._1, post_inflection._1)

          if (threads <= inflection_threads) model(threads)
          else linear((inflection_threads, model(inflection_threads)), post_inflection)
        }
      } else {
        // Piecewise linear
        val (p0, p1) =
          if (entries.head._1 < threads && threads < entries.last._1) {
            val split = entries.partition(_._1 < threads)
            (split._1.last, split._2.head)
          } else {
            val piece = if (threads < entries.head._1) entries.take(2) else entries.takeRight(2)
            (piece.head, piece.last)
          }

        linear(p0, p1)
      }
    }

    private def unify_hosts(job_name: String, on_host: String): List[(Int, Time)] = {
      def unify(hostname: String, data: Timing_Entries) =
        data.mean_time.scale(hostname_factor(hostname, on_host))

      for {
        data <- data.by_job.get(job_name).toList
        (threads, data) <- data.by_threads
        entries = data.by_hostname.toList.map(unify)
      } yield threads -> Timing_Data.median_time(entries)
    }

    def estimate_threads(job_name: String, hostname: String, threads: Int): Option[Time] = {
      def try_approximate(data: Timing_Entries): Option[Time] = {
        val entries =
          data.by_threads.toList match {
            case List((i, Timing_Entries(List(entry)))) if i != 1 =>
              (i, data.mean_time) :: entry.proper_cpu.map(1 -> _).toList
            case entries => entries.map((threads, data) => threads -> data.mean_time)
          }
        if (entries.size < 2) None else Some(approximate_threads(entries, threads))
      }

      for {
        data <- data.by_job.get(job_name)
        data <- data.by_hostname.get(hostname)
        time <- data.by_threads.get(threads).map(_.mean_time).orElse(try_approximate(data))
      } yield time
    }

    def global_threads_factor(from: Int, to: Int): Double = {
      def median(xs: Iterable[Double]): Double = xs.toList.sorted.apply(xs.size / 2)

      val estimates =
        for {
          (hostname, data) <- data.by_hostname
          job_name <- data.by_job.keys
          from_time <- estimate_threads(job_name, hostname, from)
          to_time <- estimate_threads(job_name, hostname, to)
        } yield from_time.ms.toDouble / to_time.ms

      if (estimates.nonEmpty) median(estimates)
      else {
        // unify hosts
        val estimates =
          for {
            (job_name, data) <- data.by_job
            hostname = data.by_hostname.keys.head
            entries = unify_hosts(job_name, hostname)
            if entries.length > 1
          } yield
            approximate_threads(entries, from).ms.toDouble / approximate_threads(entries, to).ms

        if (estimates.nonEmpty) median(estimates)
        else from.toDouble / to.toDouble
      }
    }

    def estimate(job_name: String, hostname: String, threads: Int): Time =
      data.by_job.get(job_name) match {
        case None =>
          // no data for job, take average of other jobs for given threads
          val job_estimates = data.by_job.keys.flatMap(estimate_threads(_, hostname, threads))
          if (job_estimates.nonEmpty) Timing_Data.mean_time(job_estimates)
          else {
            // no other job to estimate from, use global curve to approximate any other job
            val (threads1, data1) = data.by_threads.head
            data1.mean_time.scale(global_threads_factor(threads1, threads))
          }

        case Some(data) =>
          data.by_threads.get(threads) match {
            case None => // interpolate threads
              estimate_threads(job_name, hostname, threads).getOrElse {
                // per machine, try to approximate config for threads
                val approximated =
                  for {
                    hostname1 <- data.by_hostname.keys
                    estimate <- estimate_threads(job_name, hostname1, threads)
                    factor = hostname_factor(hostname1, hostname)
                  } yield estimate.scale(factor)

                if (approximated.nonEmpty) Timing_Data.mean_time(approximated)
                else {
                  // no single machine where config can be approximated, unify data points
                  val unified_entries = unify_hosts(job_name, hostname)

                  if (unified_entries.length > 1) approximate_threads(unified_entries, threads)
                  else {
                    // only single data point, use global curve to approximate
                    val (job_threads, job_time) = unified_entries.head
                    job_time.scale(global_threads_factor(job_threads, threads))
                  }
                }
              }

            case Some(data) => // time for job/thread exists, interpolate machine
              data.by_hostname.get(hostname).map(_.mean_time).getOrElse {
                Timing_Data.median_time(
                  data.by_hostname.toList.map((hostname1, data) =>
                    data.mean_time.scale(hostname_factor(hostname1, hostname))))
              }
          }
      }
  }

  object Timing_Data {
    def median_timing(obs: List[Timing]): Timing = obs.sortBy(_.elapsed.ms).apply(obs.length / 2)
    def median_time(obs: List[Time]): Time = obs.sortBy(_.ms).apply(obs.length / 2)
    def mean_time(obs: Iterable[Time]): Time = Time.ms(obs.map(_.ms).sum / obs.size)

    private def dummy_entries(host: Host, host_factor: Double) = {
      val baseline = Time.minutes(5).scale(host_factor)
      val gc = Time.seconds(10).scale(host_factor)
      List(
        Timing_Entry("dummy", host.info.hostname, 1, Timing(baseline, baseline, gc)),
        Timing_Entry("dummy", host.info.hostname, 8, Timing(baseline.scale(0.2), baseline, gc)))
    }

    def make(
      host_infos: Host_Infos,
      build_history: List[(Build_Log.Meta_Info, Build_Log.Build_Info)],
    ): Timing_Data = {
      val hosts = host_infos.hosts
      val measurements =
        for {
          (meta_info, build_info) <- build_history
          build_host = meta_info.get(Build_Log.Prop.build_host)
          (job_name, session_info) <- build_info.sessions.toList
          if build_info.finished_sessions.contains(job_name)
          hostname <- session_info.hostname.orElse(build_host).toList
          host <- hosts.find(_.info.hostname == hostname).toList
          threads = session_info.threads.getOrElse(host.info.num_cpus)
        } yield (job_name, hostname, threads) -> session_info.timing

      val entries =
        if (measurements.isEmpty) {
          val default_host = host_infos.hosts.sorted(host_infos.host_speeds).last
          host_infos.hosts.flatMap(host =>
            dummy_entries(host, host_infos.host_factor(default_host, host)))
        }
        else
          measurements.groupMap(_._1)(_._2).toList.map {
            case ((job_name, hostname, threads), timings) =>
              Timing_Entry(job_name, hostname, threads, median_timing(timings))
          }

      new Timing_Data(Timing_Entries(entries), host_infos)
    }

    def load(host_infos: Host_Infos, log_database: SQL.Database): Timing_Data = {
      val build_history =
        for {
          log_name <- log_database.execute_query_statement(
            Build_Log.private_data.meta_info_table.select(List(Build_Log.Column.log_name)),
            List.from[String], res => res.string(Build_Log.Column.log_name))
          meta_info <- Build_Log.private_data.read_meta_info(log_database, log_name)
          build_info = Build_Log.private_data.read_build_info(log_database, log_name)
        } yield (meta_info, build_info)

      make(host_infos, build_history)
    }
  }


  /* host information */

  case class Host(info: isabelle.Host.Info, build: Build_Cluster.Host)

  object Host_Infos {
    def dummy: Host_Infos =
      new Host_Infos(
        List(Host(isabelle.Host.Info("dummy", Nil, 8, Some(1.0)), Build_Cluster.Host("dummy"))))

    def load(build_hosts: List[Build_Cluster.Host], db: SQL.Database): Host_Infos = {
      def get_host(build_host: Build_Cluster.Host): Host = {
        val info =
          isabelle.Host.read_info(db, build_host.name).getOrElse(
            error("No benchmark for " + quote(build_host.name)))
        Host(info, build_host)
      }

      new Host_Infos(build_hosts.map(get_host))
    }
  }

  class Host_Infos private(val hosts: List[Host]) {
    require(hosts.nonEmpty)

    private val by_hostname = hosts.map(host => host.info.hostname -> host).toMap

    def host_factor(from: Host, to: Host): Double =
      from.info.benchmark_score.get / to.info.benchmark_score.get

    val host_speeds: Ordering[Host] =
      Ordering.fromLessThan((host1, host2) => host_factor(host1, host2) < 1)

    def the_host(hostname: String): Host =
      by_hostname.getOrElse(hostname, error("Unknown host " + quote(hostname)))
    def the_host(node_info: Node_Info): Host = the_host(node_info.hostname)

    def num_threads(node_info: Node_Info): Int =
      if (node_info.rel_cpus.nonEmpty) node_info.rel_cpus.length
      else the_host(node_info).info.num_cpus

    def available(state: Build_Process.State): Resources = {
      val allocated =
        state.running.values.map(_.node_info).groupMapReduce(the_host)(List(_))(_ ::: _)
      Resources(this, allocated)
    }
  }


  /* offline tracking of job configurations and resource allocations */

  object Config {
    def from_job(job: Build_Process.Job): Config = Config(job.name, job.node_info)
  }

  case class Config(job_name: String, node_info: Node_Info) {
    def job_of(start_time: Time): Build_Process.Job =
      Build_Process.Job(job_name, "", "", node_info, Date(start_time), None)
  }

  case class Resources(
    host_infos: Host_Infos,
    allocated_nodes: Map[Host, List[Node_Info]]
  ) {
    def unused_nodes(threads: Int): List[Node_Info] = {
      val fully_allocated =
        host_infos.hosts.foldLeft(this) { case (resources, host) =>
          if (!resources.available(host, threads)) resources
          else resources.allocate(resources.next_node(host, threads))
        }
      val used_nodes = allocated_nodes.values.flatten.toSet
      fully_allocated.allocated_nodes.values.flatten.toList.filterNot(used_nodes.contains)
    }

    def allocated(host: Host): List[Node_Info] = allocated_nodes.getOrElse(host, Nil)

    def allocate(node: Node_Info): Resources = {
      val host = host_infos.the_host(node)
      copy(allocated_nodes = allocated_nodes + (host -> (node :: allocated(host))))
    }

    def try_allocate_tasks(
      hosts: List[(Host, Int)],
      tasks: List[(Build_Process.Task, Int, Int)],
    ): (List[Config], Resources) =
      tasks match {
        case Nil => (Nil, this)
        case (task, min_threads, max_threads) :: tasks =>
          val (config, resources) =
            hosts.find((host, _) => available(host, min_threads)) match {
              case Some((host, host_max_threads)) =>
                val free_threads = host.info.num_cpus - ((host.build.jobs - 1) * host_max_threads)
                val node_info = next_node(host, (min_threads max free_threads) min max_threads)
                (Some(Config(task.name, node_info)), allocate(node_info))
              case None => (None, this)
            }
          val (configs, resources1) = resources.try_allocate_tasks(hosts, tasks)
          (configs ++ config, resources1)
      }

    def next_node(host: Host, threads: Int): Node_Info = {
      val numa_node_num_cpus = host.info.num_cpus / (host.info.numa_nodes.length max 1)
      def explicit_cpus(node_info: Node_Info): List[Int] =
        if (node_info.rel_cpus.nonEmpty) node_info.rel_cpus else (0 until numa_node_num_cpus).toList

      val used_nodes = allocated(host).groupMapReduce(_.numa_node)(explicit_cpus)(_ ::: _)

      val available_nodes = host.info.numa_nodes
      val numa_node =
        if (!host.build.numa) None
        else available_nodes.sortBy(n => used_nodes.getOrElse(Some(n), Nil).length).headOption

      val used_cpus = used_nodes.getOrElse(numa_node, Nil).toSet
      val available_cpus = (0 until numa_node_num_cpus).filterNot(used_cpus.contains).toList

      val rel_cpus = if (available_cpus.length >= threads) available_cpus.take(threads) else Nil

      Node_Info(host.info.hostname, numa_node, rel_cpus)
    }

    def available(host: Host, threads: Int): Boolean = {
      val used = allocated(host)

      if (used.length >= host.build.jobs) false
      else {
        if (host.info.numa_nodes.length <= 1)
          used.map(host_infos.num_threads).sum + threads <= host.info.num_cpus
        else {
          def node_threads(n: Int): Int =
            used.filter(_.numa_node.contains(n)).map(host_infos.num_threads).sum

          host.info.numa_nodes.exists(
            node_threads(_) + threads <= host.info.num_cpus / host.info.numa_nodes.length)
        }
      }
    }
  }


  /* schedule generation */

  object Schedule {
    case class Node(job_name: String, node_info: Node_Info, start: Date, duration: Time) {
      def end: Date = Date(start.time + duration)
    }

    type Graph = isabelle.Graph[String, Node]
  }

  case class Schedule(start: Date, graph: Schedule.Graph) {
    def end: Date =
      if (graph.is_empty) start
      else graph.maximals.map(graph.get_node).map(_.end).maxBy(_.unix_epoch)

    def duration: Time = end.time - start.time
  }

  case class State(build_state: Build_Process.State, current_time: Time, finished: Schedule) {
    def start(config: Config): State =
      copy(build_state =
        build_state.copy(running = build_state.running +
          (config.job_name -> config.job_of(current_time))))

    def step(timing_data: Timing_Data): State = {
      val remaining =
        build_state.running.values.toList.map { job =>
          val elapsed = current_time - job.start_date.time
          val threads = timing_data.host_infos.num_threads(job.node_info)
          val predicted = timing_data.estimate(job.name, job.node_info.hostname, threads)
          val remaining = if (elapsed > predicted) Time.zero else predicted - elapsed
          job -> remaining
        }

      if (remaining.isEmpty) error("Schedule step without running sessions")
      else {
        val (job, elapsed) = remaining.minBy(_._2.ms)
        val now = current_time + elapsed
        val node = Schedule.Node(job.name, job.node_info, job.start_date, now - job.start_date.time)

        val preds =
          build_state.sessions.graph.imm_preds(job.name).filter(finished.graph.defined)
        val graph =
          preds.foldLeft(finished.graph.new_node(job.name, node))(_.add_edge(_, job.name))

        val build_state1 = build_state.remove_running(job.name).remove_pending(job.name)
        State(build_state1, now, finished.copy(graph = graph))
      }
    }

    def is_finished: Boolean = build_state.pending.isEmpty && build_state.running.isEmpty
  }

  trait Scheduler {
    def next(state: Build_Process.State): List[Config]
    def build_schedule(build_state: Build_Process.State): Schedule
  }

  abstract class Heuristic(timing_data: Timing_Data, max_threads_limit: Int) extends Scheduler {
    val host_infos = timing_data.host_infos
    val ordered_hosts = host_infos.hosts.sorted(host_infos.host_speeds)
    val max_threads = host_infos.hosts.map(_.info.num_cpus).max min max_threads_limit

    def best_time(job_name: String): Time = {
      val host = ordered_hosts.last
      val threads = timing_data.best_threads(job_name, max_threads) min host.info.num_cpus
      timing_data.estimate(job_name, host.info.hostname, threads)
    }

    def build_schedule(build_state: Build_Process.State): Schedule = {
      @tailrec
      def simulate(state: State): State =
        if (state.is_finished) state
        else {
          val state1 = next(state.build_state).foldLeft(state)(_.start(_)).step(timing_data)
          simulate(state1)
        }

      val start = Date.now()
      val end_state = simulate(State(build_state, start.time, Schedule(start, Graph.empty)))

      end_state.finished
    }
  }

  class Meta_Heuristic(heuristics: List[Heuristic]) extends Scheduler {
    require(heuristics.nonEmpty)

    def best_result(state: Build_Process.State): (Heuristic, Schedule) =
      heuristics.map(heuristic =>
        heuristic -> heuristic.build_schedule(state)).minBy(_._2.duration.ms)

    def next(state: Build_Process.State): List[Config] = best_result(state)._1.next(state)

    def build_schedule(state: Build_Process.State): Schedule = best_result(state)._2
  }


  /* heuristics */

  abstract class Path_Heuristic(
    timing_data: Timing_Data,
    sessions_structure: Sessions.Structure,
    max_threads_limit: Int
  ) extends Heuristic(timing_data, max_threads_limit) {
    /* pre-computed properties for efficient heuristic */

    type Node = String

    val build_graph = sessions_structure.build_graph

    val minimals = build_graph.minimals
    val maximals = build_graph.maximals

    def all_preds(node: Node): Set[Node] = build_graph.all_preds(List(node)).toSet
    val maximals_all_preds = maximals.map(node => node -> all_preds(node)).toMap

    val best_times = build_graph.keys.map(node => node -> best_time(node)).toMap

    val succs_max_time_ms = build_graph.node_height(best_times(_).ms)
    def max_time(node: Node): Time = Time.ms(succs_max_time_ms(node)) + best_times(node)
    def max_time(task: Build_Process.Task): Time = max_time(task.name)

    def path_times(minimals: List[Node]): Map[Node, Time] = {
      def time_ms(node: Node): Long = best_times(node).ms
      val path_times_ms = build_graph.reachable_length(time_ms, build_graph.imm_succs, minimals)
      path_times_ms.view.mapValues(Time.ms).toMap
    }

    def path_max_times(minimals: List[Node]): Map[Node, Time] =
      path_times(minimals).toList.map((node, time) => node -> (time + max_time(node))).toMap

    def parallel_paths(minimals: List[Node], pred: Node => Boolean = _ => true): Int = {
      def start(node: Node): (Node, Time) = node -> best_times(node)

      def pass_time(elapsed: Time)(node: Node, time: Time): (Node, Time) =
        node -> (time - elapsed)

      def parallel_paths(running: Map[Node, Time]): (Int, Map[Node, Time]) =
        if (running.isEmpty) (0, running)
        else {
          def get_next(node: Node): List[Node] =
            build_graph.imm_succs(node).filter(pred).filter(
              build_graph.imm_preds(_).intersect(running.keySet).isEmpty).toList

          val (next, elapsed) = running.minBy(_._2.ms)
          val (remaining, finished) =
            running.toList.map(pass_time(elapsed)).partition(_._2 > Time.zero)

          val running1 =
            remaining.map(pass_time(elapsed)).toMap ++
              finished.map(_._1).flatMap(get_next).map(start)
          val (res, running2) = parallel_paths(running1)
          (res max running1.size, running2)
        }

      parallel_paths(minimals.map(start).toMap)._1
    }
  }

  class Timing_Heuristic(
    threshold: Time,
    timing_data: Timing_Data,
    sessions_structure: Sessions.Structure,
    max_threads_limit: Int = 8
  ) extends Path_Heuristic(timing_data, sessions_structure, max_threads_limit) {

    def next(state: Build_Process.State): List[Config] = {
      val resources = host_infos.available(state)

      def best_threads(task: Build_Process.Task): Int =
        timing_data.best_threads(task.name, max_threads)

      val rev_ordered_hosts = ordered_hosts.reverse.map(_ -> max_threads)

      val resources0 = host_infos.available(state.copy(running = Map.empty))
      val max_parallel = parallel_paths(state.ready.map(_.name))
      val fully_parallelizable = max_parallel <= resources0.unused_nodes(max_threads).length

      val next_sorted = state.next_ready.sortBy(max_time(_).ms).reverse

      if (fully_parallelizable) {
        val all_tasks = next_sorted.map(task => (task, best_threads(task), best_threads(task)))
        resources.try_allocate_tasks(rev_ordered_hosts, all_tasks)._1
      }
      else {
        val critical_minimals = state.ready.filter(max_time(_) > threshold).map(_.name)
        val critical_nodes = path_max_times(critical_minimals).filter(_._2 > threshold).keySet

        val (critical, other) = next_sorted.partition(task => critical_nodes.contains(task.name))

        val critical_tasks = critical.map(task => (task, best_threads(task), best_threads(task)))
        val other_tasks = other.map(task => (task, 1, best_threads(task)))

        val max_critical_parallel = parallel_paths(critical_minimals, critical_nodes.contains)
        val (critical_hosts, other_hosts) = rev_ordered_hosts.splitAt(max_critical_parallel)

        val (configs1, resources1) = resources.try_allocate_tasks(critical_hosts, critical_tasks)
        val (configs2, _) = resources1.try_allocate_tasks(other_hosts, other_tasks)

        configs1 ::: configs2
      }
    }
  }


  /* process for scheduled build */

  abstract class Scheduled_Build_Process(
    build_context: Build.Context,
    build_progress: Progress,
    server: SSH.Server,
  ) extends Build_Process(build_context, build_progress, server) {
    protected val start_date = Date.now()

    def init_scheduler(timing_data: Timing_Data): Scheduler

    /* global resources with common close() operation */

    private final lazy val _log_store: Build_Log.Store = Build_Log.store(build_options)
    private final lazy val _log_database: SQL.Database =
      try {
        val db = _log_store.open_database(server = this.server)
        _log_store.init_database(db)
        db
      }
      catch { case exn: Throwable => close(); throw exn }

    override def close(): Unit = {
      super.close()
      Option(_log_database).foreach(_.close())
    }


    /* previous results via build log */

    override def open_build_cluster(): Build_Cluster = {
      val build_cluster = super.open_build_cluster()
      build_cluster.init()
      if (build_context.master && build_context.max_jobs > 0) {
        val benchmark_options = build_options.string("build_hostname") = hostname
        Benchmark.benchmark(benchmark_options, progress)
      }
      build_cluster.benchmark()
      build_cluster
    }

    private val timing_data: Timing_Data = {
      val cluster_hosts: List[Build_Cluster.Host] =
        if (build_context.max_jobs == 0) build_context.build_hosts
        else {
          val local_build_host =
            Build_Cluster.Host(
              hostname, jobs = build_context.max_jobs, numa = build_context.numa_shuffling)
          local_build_host :: build_context.build_hosts
        }

      val host_infos = Host_Infos.load(cluster_hosts, _host_database)
      Timing_Data.load(host_infos, _log_database)
    }
    private val scheduler = init_scheduler(timing_data)

    def write_build_log(results: Build.Results, state: Build_Process.State.Results): Unit = {
      val sessions =
        for {
          (session_name, result) <- state.toList
          if !result.current
        } yield {
          val info = build_context.sessions_structure(session_name)
          val entry =
            if (!results.cancelled(session_name)) {
              val status =
                if (result.ok) Build_Log.Session_Status.finished
                else Build_Log.Session_Status.failed

              Build_Log.Session_Entry(
                chapter = info.chapter,
                groups = info.groups,
                hostname = Some(result.node_info.hostname),
                threads = Some(timing_data.host_infos.num_threads(result.node_info)),
                timing = result.process_result.timing,
                sources = Some(result.output_shasum.digest.toString),
                status = Some(status))
            }
            else
              Build_Log.Session_Entry(
                chapter = info.chapter,
                groups = info.groups,
                status = Some(Build_Log.Session_Status.cancelled))
          session_name -> entry
        }

      val settings =
        Build_Log.Settings.all_settings.map(_.name).map(name =>
          name -> Isabelle_System.getenv(name))
      val props =
        List(
          Build_Log.Prop.build_id.name -> build_context.build_uuid,
          Build_Log.Prop.build_engine.name -> build_context.engine.name,
          Build_Log.Prop.build_host.name -> hostname,
          Build_Log.Prop.build_start.name -> Build_Log.print_date(start_date))

      val meta_info = Build_Log.Meta_Info(props, settings)
      val build_info = Build_Log.Build_Info(sessions.toMap)
      val log_name = Build_Log.log_filename(engine = build_context.engine.name, date = start_date)

      Build_Log.private_data.update_sessions(
        _log_database, _log_store.cache.compress, log_name.file_name, build_info)
      Build_Log.private_data.update_meta_info(_log_database, log_name.file_name, meta_info)
    }


    /* build process */

    case class Cache(state: Build_Process.State, configs: List[Config], estimate: Date) {
      def is_current(state: Build_Process.State): Boolean =
        this.state.pending.nonEmpty && this.state.results == state.results
      def is_current_estimate(estimate: Date): Boolean =
        Math.abs((this.estimate.time - estimate.time).ms) < Time.minutes(1).ms
    }

    private var cache = Cache(Build_Process.State(), Nil, Date.now())

    override def next_node_info(state: Build_Process.State, session_name: String): Node_Info = {
      val configs =
        if (cache.is_current(state)) cache.configs
        else scheduler.next(state)
      configs.find(_.job_name == session_name).get.node_info
    }

    def is_current(state: Build_Process.State, session_name: String): Boolean =
      state.ancestor_results(session_name) match {
        case Some(ancestor_results) if ancestor_results.forall(_.current) =>
          val sources_shasum = state.sessions(session_name).sources_shasum

          val input_shasum =
            if (ancestor_results.isEmpty) ML_Process.bootstrap_shasum()
            else SHA1.flat_shasum(ancestor_results.map(_.output_shasum))

          val store_heap =
            build_context.build_heap || Sessions.is_pure(session_name) ||
              state.sessions.iterator.exists(_.ancestors.contains(session_name))

          store.check_output(
            _database_server, session_name,
            session_options = build_context.sessions_structure(session_name).options,
            sources_shasum = sources_shasum,
            input_shasum = input_shasum,
            fresh_build = build_context.fresh_build,
            store_heap = store_heap)._1
        case _ => false
    }

    override def next_jobs(state: Build_Process.State): List[String] = {
      val finalize_limit = if (build_context.master) Int.MaxValue else 0

      if (progress.stopped) state.next_ready.map(_.name).take(finalize_limit)
      else if (cache.is_current(state)) cache.configs.map(_.job_name).filterNot(state.is_running)
      else {
        val current = state.next_ready.filter(task => is_current(state, task.name))
        if (current.nonEmpty) current.map(_.name).take(finalize_limit)
        else {
          val start = Time.now()
          val next = scheduler.next(state)
          val estimate = Date(Time.now() + scheduler.build_schedule(state).duration)
          val elapsed = Time.now() - start

          val timing_msg = if (elapsed.is_relevant) " (took " + elapsed.message + ")" else ""
          progress.echo_if(build_context.master && !cache.is_current_estimate(estimate),
            "Estimated completion: " + estimate + timing_msg)

          val configs = next.filter(_.node_info.hostname == hostname)
          cache = Cache(state, configs, estimate)
          configs.map(_.job_name)
        }
      }
    }

    override def run(): Build.Results = {
      val results = super.run()
      if (build_context.master) write_build_log(results, snapshot().results)
      results
    }
  }

  class Engine extends Build.Engine("build_schedule") {

    def scheduler(timing_data: Timing_Data, sessions_structure: Sessions.Structure): Scheduler = {
      val heuristics =
        List(5, 10, 20).map(minutes =>
          Timing_Heuristic(Time.minutes(minutes), timing_data, sessions_structure))
      new Meta_Heuristic(heuristics)
    }

    override def open_build_process(
      context: Build.Context,
      progress: Progress,
      server: SSH.Server
    ): Build_Process =
      new Scheduled_Build_Process(context, progress, server) {
        def init_scheduler(timing_data: Timing_Data): Scheduler =
          scheduler(timing_data, context.sessions_structure)
      }
  }


  /* build schedule */

  def build_schedule(
    options: Options,
    build_hosts: List[Build_Cluster.Host] = Nil,
    selection: Sessions.Selection = Sessions.Selection.empty,
    progress: Progress = new Progress,
    afp_root: Option[Path] = None,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    infos: List[Sessions.Info] = Nil,
    numa_shuffling: Boolean = false,
    augment_options: String => List[Options.Spec] = _ => Nil,
    session_setup: (String, Session) => Unit = (_, _) => (),
    cache: Term.Cache = Term.Cache.make()
  ): Schedule = {
    val build_engine = new Engine

    val store = build_engine.build_store(options, build_hosts = build_hosts, cache = cache)
    val log_store = Build_Log.store(options, cache = cache)
    val build_options = store.options

    def build_schedule(
      server: SSH.Server,
      database_server: Option[SQL.Database],
      log_database: PostgreSQL.Database,
      host_database: SQL.Database
    ): Schedule = {
      val full_sessions =
        Sessions.load_structure(build_options, dirs = AFP.make_dirs(afp_root) ::: dirs,
          select_dirs = select_dirs, infos = infos, augment_options = augment_options)
      val full_sessions_selection = full_sessions.imports_selection(selection)

      val build_deps =
        Sessions.deps(full_sessions.selection(selection), progress = progress,
          inlined_files = true).check_errors

      val build_context =
        Build.Context(store, build_engine, build_deps, afp_root = afp_root,
          build_hosts = build_hosts, hostname = Build.hostname(build_options),
          numa_shuffling = numa_shuffling, max_jobs = 0, session_setup = session_setup,
          master = true)

      val cluster_hosts = build_context.build_hosts

      val hosts_current =
        cluster_hosts.forall(host => isabelle.Host.read_info(host_database, host.name).isDefined)
      if (!hosts_current) {
        val build_cluster = Build_Cluster.make(build_context, progress = progress)
        build_cluster.open()
        build_cluster.init()
        build_cluster.benchmark()
        build_cluster.close()
      }

      val host_infos = Host_Infos.load(cluster_hosts, host_database)
      val timing_data = Timing_Data.load(host_infos, log_database)

      val sessions = Build_Process.Sessions.empty.init(build_context, database_server, progress)
      def task(session: Build_Job.Session_Context): Build_Process.Task =
        Build_Process.Task(session.name, session.deps, JSON.Object.empty, build_context.build_uuid)

      val build_state =
        Build_Process.State(sessions = sessions, pending = sessions.iterator.map(task).toList)

      val scheduler = build_engine.scheduler(timing_data, build_context.sessions_structure)
      scheduler.build_schedule(build_state)
    }

    using(store.open_server()) { server =>
      using_optional(store.maybe_open_database_server(server = server)) { database_server =>
        using(log_store.open_database(server = server)) { log_database =>
          using(store.open_build_database(
            path = isabelle.Host.private_data.database, server = server)) { host_database =>
              build_schedule(server, database_server, log_database, host_database)
          }
        }
      }
    }
  }
}
