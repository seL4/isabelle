/*  Title:      Pure/Admin/build_history.scala
    Author:     Makarius

Build other history versions.
*/

package isabelle


object Build_History {
  /* log files */

  val engine = "build_history"
  val log_prefix = engine + "_"


  /* augment settings */

  def make_64_32(platform: String): String =
    platform.replace("x86_64-", "x86_64_32-").replace("arm64-", "arm64_32-")

  def augment_settings(
    other_isabelle: Other_Isabelle,
    threads: Int,
    arch_64: Boolean,
    arch_apple: Boolean,
    heap: Int,
    max_heap: Option[Int],
    more_settings: List[String]
  ): String = {
    val (ml_platform, ml_settings) = {
      val cygwin_32 = "x86-cygwin"
      val windows_32 = "x86-windows"
      val windows_64 = "x86_64-windows"
      val windows_64_32 = "x86_64_32-windows"
      val platform_32 = other_isabelle.getenv("ISABELLE_PLATFORM32")
      val platform_64 = other_isabelle.getenv("ISABELLE_PLATFORM64")
      val platform_64_32 = make_64_32(platform_64)
      val platform_apple_64 = other_isabelle.getenv("ISABELLE_APPLE_PLATFORM64")
      val platform_apple_64_32 = make_64_32(platform_apple_64)

      val polyml_home =
        try { Path.explode(other_isabelle.getenv("ML_HOME")).dir }
        catch { case ERROR(msg) => error("Bad ML_HOME: " + msg) }

      def ml_home(platform: String): Path = polyml_home + Path.explode(platform)

      def err(platform: String): Nothing =
        error("Platform " + platform + " unavailable on this machine")

      def check_dir(platform: String): Boolean =
        platform != "" && ml_home(platform).is_dir

      val ml_platform =
        if (Platform.is_windows && arch_64) {
          if (check_dir(windows_64)) windows_64 else err(windows_64)
        }
        else if (Platform.is_windows && !arch_64) {
          if (check_dir(windows_64_32)) windows_64_32
          else if (check_dir(cygwin_32)) cygwin_32
          else if (check_dir(windows_32)) windows_32
          else err(windows_32)
        }
        else if (arch_apple && arch_64) {
          if (check_dir(platform_apple_64)) platform_apple_64 else err(platform_apple_64)
        }
        else if (arch_apple) {
          if (check_dir(platform_apple_64_32)) platform_apple_64_32 else err(platform_apple_64_32)
        }
        else if (arch_64) {
          if (check_dir(platform_64)) platform_64 else err(platform_64)
        }
        else if (check_dir(platform_64_32)) platform_64_32
        else platform_32

      val ml_options =
        "--minheap " + heap + (if (max_heap.isDefined) " --maxheap " + max_heap.get else "") +
        " --gcthreads " + threads +
        (if (ml_platform.endsWith("-windows")) " --codepage utf8" else "")

      (ml_platform,
        List(
          "ML_HOME=" + File.bash_path(ml_home(ml_platform)),
          "ML_PLATFORM=" + quote(ml_platform),
          "ML_OPTIONS=" + quote(ml_options)))
    }

    val thread_settings =
      List(
        "ISABELLE_JAVA_SYSTEM_OPTIONS=\"$ISABELLE_JAVA_SYSTEM_OPTIONS -Disabelle.threads=" + threads + "\"",
        "ISABELLE_BUILD_OPTIONS=\"threads=" + threads + "\"")

    val settings =
      List(ml_settings, thread_settings) :::
      (if (more_settings.isEmpty) Nil else List(more_settings))

    File.append(other_isabelle.etc_settings, "\n" + cat_lines(settings.map(terminate_lines(_))))

    ml_platform
  }



  /** local build **/

  private val default_multicore = (1, 1)
  private val default_heap = 1500
  private val default_isabelle_identifier = "build_history"

  def local_build(
    options: Options,
    root: Path,
    progress: Progress = new Progress,
    afp: Boolean = false,
    isabelle_identifier: String = default_isabelle_identifier,
    ml_statistics_step: Int = 1,
    component_repository: String = Components.static_component_repository,
    components_base: String = Components.dynamic_components_base,
    clean_platforms: Option[List[Platform.Family]] = None,
    clean_archives: Boolean = false,
    fresh: Boolean = false,
    hostname: String = "",
    multicore_base: Boolean = false,
    multicore_list: List[(Int, Int)] = List(default_multicore),
    arch_64: Boolean = false,
    arch_apple: Boolean = false,
    heap: Int = default_heap,
    max_heap: Option[Int] = None,
    more_settings: List[String] = Nil,
    more_preferences: List[String] = Nil,
    verbose: Boolean = false,
    build_tags: List[String] = Nil,
    build_args: List[String] = Nil
  ): List[(Process_Result, Path)] = {
    /* sanity checks */

    if (File.eq(Path.ISABELLE_HOME, root)) {
      error("Repository coincides with ISABELLE_HOME=" + Path.ISABELLE_HOME.expand)
    }

    for ((threads, _) <- multicore_list if threads < 1) {
      error("Bad threads value < 1: " + threads)
    }
    for ((_, processes) <- multicore_list if processes < 1) {
      error("Bad processes value < 1: " + processes)
    }

    if (heap < 100) error("Bad heap value < 100: " + heap)

    if (max_heap.isDefined && max_heap.get < heap) {
      error("Bad max_heap value < heap: " + max_heap.get)
    }

    System.getenv("ISABELLE_SETTINGS_PRESENT") match {
      case null | "" =>
      case _ => error("Cannot run Admin/build_other within existing Isabelle settings environment")
    }


    /* Isabelle + AFP directory */

    def directory(dir: Path): Mercurial.Hg_Sync.Directory = {
      val directory = Mercurial.Hg_Sync.directory(dir)
      if (verbose) progress.echo(directory.log)
      directory
    }

    val isabelle_directory = directory(root)
    val (afp_directory, afp_build_args) =
      if (afp) (Some(directory(root + Path.explode("AFP"))), List("-d", "~~/dirs/AFP/thys"))
      else (None, Nil)


    /* main */

    val other_isabelle =
      Other_Isabelle(root, isabelle_identifier = isabelle_identifier, progress = progress)

    def resolve_components(): Unit =
      other_isabelle.resolve_components(
        echo = verbose,
        component_repository = component_repository,
        clean_platforms = clean_platforms,
        clean_archives = clean_archives)

    val build_host = proper_string(hostname) getOrElse Isabelle_System.hostname()
    val build_history_date = progress.now()
    val build_group_id = build_host + ":" + build_history_date.time.ms

    var first_build = true
    for ((threads, processes) <- multicore_list) yield {
      /* init settings */

      val component_settings =
        other_isabelle.init_components(
          components_base = components_base,
          catalogs = Components.optional_catalogs)
      other_isabelle.init_settings(component_settings)
      resolve_components()
      val ml_platform =
        augment_settings(
          other_isabelle, threads, arch_64, arch_apple, heap, max_heap, more_settings)

      File.write(other_isabelle.etc_preferences,
        cat_lines("build_log_verbose = true" :: more_preferences))

      val isabelle_output =
        other_isabelle.expand_path(
          Path.explode("$ISABELLE_HOME_USER/heaps/$ML_IDENTIFIER"))
      val isabelle_output_log = isabelle_output + Path.explode("log")
      val isabelle_base_log = isabelle_output + Path.explode("../base_log")

      if (first_build) {
        resolve_components()
        other_isabelle.scala_build(fresh = fresh, echo = verbose)
        Setup_Tool.init(other_isabelle, verbose = verbose)
        Isabelle_System.rm_tree(isabelle_base_log)
      }

      Isabelle_System.rm_tree(isabelle_output)
      Isabelle_System.make_directory(isabelle_output)

      other_isabelle.expand_path(Path.explode("$ISABELLE_HOME_USER/mash_state")).file.delete

      val log_path =
        other_isabelle.isabelle_home_user +
          Build_Log.log_subdir(build_history_date) +
          Build_Log.log_filename(Build_History.engine, build_history_date,
            List(build_host, ml_platform, "M" + threads) ::: build_tags)

      Isabelle_System.make_directory(log_path.dir)

      val build_out = other_isabelle.expand_path(Path.explode("$ISABELLE_HOME_USER/log/build.out"))
      val build_out_progress = new File_Progress(build_out)
      build_out.file.delete


      /* build */

      if (multicore_base && !first_build && isabelle_base_log.is_dir) {
        Isabelle_System.copy_dir(isabelle_base_log, isabelle_output_log)
      }

      val build_start = progress.now()
      val build_args1 = List("-v", "-j" + processes) ::: afp_build_args ::: build_args

      val build_result =
        Other_Isabelle(root, isabelle_identifier = isabelle_identifier,
          progress = build_out_progress)
        .bash("bin/isabelle build " + Bash.strings(build_args1),
          redirect = true, echo = true, strict = false)

      val build_end = progress.now()

      val store = Store(options + "build_database_server=false")

      val build_info: Build_Log.Build_Info =
        Build_Log.Log_File(log_path.file_name, build_result.out_lines, cache = store.cache).
          parse_build_info(ml_statistics = true)


      /* output log */

      val meta_info =
        Properties.lines_nonempty(Build_Log.Prop.build_tags.name, build_tags) :::
        Properties.lines_nonempty(Build_Log.Prop.build_args.name, build_args1) :::
        List(
          Build_Log.Prop.build_group_id.name -> build_group_id,
          Build_Log.Prop.build_id.name -> (build_host + ":" + build_start.time.ms),
          Build_Log.Prop.build_engine.name -> Build_History.engine,
          Build_Log.Prop.build_host.name -> build_host,
          Build_Log.Prop.build_start.name -> Build_Log.print_date(build_start),
          Build_Log.Prop.build_end.name -> Build_Log.print_date(build_end),
          Build_Log.Prop.isabelle_version.name -> isabelle_directory.id) :::
        afp_directory.map(dir => Build_Log.Prop.afp_version.name -> dir.id).toList

      build_out_progress.echo("Reading session build info ...")
      val session_build_info =
        build_info.finished_sessions.flatMap { session_name =>
          val database = isabelle_output + Store.log_db(session_name)

          if (database.is_file) {
            using(SQLite.open_database(database)) { db =>
              val theory_timings =
                try {
                  store.read_theory_timings(db, session_name).map(ps =>
                    Protocol.Theory_Timing_Marker((Build_Log.SESSION_NAME, session_name) :: ps))
                }
                catch { case ERROR(_) => Nil }

              val session_sources =
                store.read_build(db, session_name).map(_.sources) match {
                  case Some(sources) if !sources.is_empty =>
                    List("Sources " + session_name + " " + sources.digest.toString)
                  case _ => Nil
                }

              theory_timings ::: session_sources
            }
          }
          else Nil
        }

      build_out_progress.echo("Reading ML statistics ...")
      val ml_statistics =
        build_info.finished_sessions.flatMap { session_name =>
          val database = isabelle_output + Store.log_db(session_name)
          val log_gz = isabelle_output + Store.log_gz(session_name)

          val properties =
            if (database.is_file) {
              using(SQLite.open_database(database))(store.read_ml_statistics(_, session_name))
            }
            else if (log_gz.is_file) {
              Build_Log.Log_File.read(log_gz.file, cache = store.cache)
                .parse_session_info(ml_statistics = true).ml_statistics
            }
            else Nil

          val trimmed_properties =
            if (ml_statistics_step <= 0) Nil
            else if (ml_statistics_step == 1) properties
            else {
              (for { (ps, i) <- properties.iterator.zipWithIndex if i % ml_statistics_step == 0 }
               yield ps).toList
            }

          trimmed_properties.map(ps => (Build_Log.SESSION_NAME -> session_name) :: ps)
        }

      build_out_progress.echo("Reading error messages ...")
      val session_errors =
        build_info.failed_sessions.flatMap { session_name =>
          val database = isabelle_output + Store.log_db(session_name)
          val errors =
            if (database.is_file) {
              try {
                using(SQLite.open_database(database))(store.read_errors(_, session_name))
              } // column "errors" could be missing
              catch { case _: java.sql.SQLException => Nil }
            }
            else Nil
          for (msg <- errors)
          yield {
            val content = Library.encode_lines(Output.clean_yxml(msg))
            List(Build_Log.SESSION_NAME -> session_name, Markup.CONTENT -> content)
          }
        }

      build_out_progress.echo("Reading heap sizes ...")
      val heap_sizes =
        build_info.finished_sessions.flatMap { session_name =>
          val heap = isabelle_output + Path.explode(session_name)
          if (heap.is_file) {
            Some("Heap " + session_name + " (" + Value.Long(File.size(heap)) + " bytes)")
          }
          else None
        }

      build_out_progress.echo("Writing log file " + log_path.xz + " ...")
      File.write_xz(log_path.xz,
        terminate_lines(
          Protocol.Meta_Info_Marker(meta_info) :: build_result.out_lines :::
          session_build_info :::
          ml_statistics.map(Protocol.ML_Statistics_Marker.apply) :::
          session_errors.map(Protocol.Error_Message_Marker.apply) :::
          heap_sizes), Compress.Options_XZ(6))


      /* next build */

      if (multicore_base && first_build && isabelle_output_log.is_dir) {
        Isabelle_System.copy_dir(isabelle_output_log, isabelle_base_log)
      }

      Isabelle_System.rm_tree(isabelle_output)

      first_build = false

      (build_result, log_path.xz)
    }
  }


  /* command line entry point */

  private object Multicore {
    private val Pat1 = """^(\d+)$""".r
    private val Pat2 = """^(\d+)x(\d+)$""".r

    def parse(s: String): (Int, Int) =
      s match {
        case Pat1(Value.Int(x)) => (x, 1)
        case Pat2(Value.Int(x), Value.Int(y)) => (x, y)
        case _ => error("Bad multicore configuration: " + quote(s))
      }
  }

  def main(args: Array[String]): Unit = {
    Command_Line.tool {
      var afp = false
      var multicore_base = false
      var heap: Option[Int] = None
      var max_heap: Option[Int] = None
      var multicore_list = List(default_multicore)
      var isabelle_identifier = default_isabelle_identifier
      var clean_platforms: Option[List[Platform.Family]] = None
      var clean_archives = false
      var component_repository = Components.static_component_repository
      var components_base = Components.dynamic_components_base
      var arch_apple = false
      var more_settings: List[String] = Nil
      var more_preferences: List[String] = Nil
      var fresh = false
      var hostname = ""
      var arch_64 = false
      var output_file = ""
      var ml_statistics_step = 1
      var build_tags = List.empty[String]
      var verbose = false
      var exit_code = false

      val getopts = Getopts("""
Usage: Admin/build_other [OPTIONS] ISABELLE_HOME [ARGS ...]

  Options are:
    -A           include $ISABELLE_HOME/AFP directory
    -B           first multicore build serves as base for scheduling information
    -H SIZE      minimal ML heap in MB (default: """ + default_heap + """ for 32bit, """ +
      default_heap * 2 + """ for 64bit)
    -M MULTICORE multicore configurations (see below)
    -N NAME      alternative ISABELLE_IDENTIFIER (default: """ + default_isabelle_identifier + """)
    -O PLATFORMS clean resolved components, retaining only the given list
                 platform families (separated by commas; default: do nothing)
    -Q           clean archives of downloaded components
    -R URL       remote repository for Isabelle components (default: """ +
      Components.static_component_repository + """)
    -S DIR       base directory for Isabelle components (default: """ +
      quote(Components.dynamic_components_base) + """)
    -U SIZE      maximal ML heap in MB (default: unbounded)
    -a           processor architecture is Apple Silicon (ARM64)
    -e TEXT      additional text for generated etc/settings
    -f           fresh build of Isabelle/Scala components (recommended)
    -h NAME      override local hostname
    -i TEXT      initial text for generated etc/settings
    -m ARCH      processor architecture (32, 64, default: 32)
    -n           no build: sync only
    -o FILE      output file for log names (default: stdout)
    -p TEXT      additional text for generated etc/preferences
    -s NUMBER    step size for ML statistics (0=none, 1=all, n=step, default: 1)
    -t TAG       free-form build tag (multiple occurrences possible)
    -v           verbose
    -x           return overall exit code from build processes

  Build Isabelle sessions from the history of another REPOSITORY clone,
  passing ARGS directly to its isabelle build tool.

  Each MULTICORE configuration consists of one or two numbers (default 1):
  THREADS or THREADSxPROCESSES, e.g. -M 1,2,4 or -M 1x4,2x2,4.
""",
        "A" -> (_ => afp = true),
        "B" -> (_ => multicore_base = true),
        "H:" -> (arg => heap = Some(Value.Int.parse(arg))),
        "M:" -> (arg => multicore_list = space_explode(',', arg).map(Multicore.parse)),
        "N:" -> (arg => isabelle_identifier = arg),
        "O:" -> (arg => clean_platforms = Some(space_explode(',',arg).map(Platform.Family.parse))),
        "Q" -> (_ => clean_archives = true),
        "R:" -> (arg => component_repository = arg),
        "S:" -> (arg => components_base = arg),
        "U:" -> (arg => max_heap = Some(Value.Int.parse(arg))),
        "a" -> (_ => arch_apple = true),
        "e:" -> (arg => more_settings = more_settings ::: List(arg)),
        "f" -> (_ => fresh = true),
        "h:" -> (arg => hostname = arg),
        "m:" ->
          {
            case "32" => arch_64 = false
            case "64" => arch_64 = true
            case bad => error("Bad processor architecture: " + quote(bad))
          },
        "o:" -> (arg => output_file = arg),
        "p:" -> (arg => more_preferences = more_preferences ::: List(arg)),
        "s:" -> (arg => ml_statistics_step = Value.Int.parse(arg)),
        "t:" -> (arg => build_tags = build_tags ::: List(arg)),
        "v" -> (_ => verbose = true),
        "x" -> (_ => exit_code = true))

      val more_args = getopts(args)
      val (root, build_args) =
        more_args match {
          case root :: build_args => (Path.explode(root), build_args)
          case _ => getopts.usage()
        }

      val progress = new Console_Progress(stderr = true)

      val results =
        local_build(Options.init(), root, progress = progress, afp = afp,
          isabelle_identifier = isabelle_identifier, ml_statistics_step = ml_statistics_step,
          component_repository = component_repository, components_base = components_base,
          clean_platforms = clean_platforms, clean_archives = clean_archives,
          fresh = fresh, hostname = hostname, multicore_base = multicore_base,
          multicore_list = multicore_list, arch_64 = arch_64, arch_apple = arch_apple,
          heap = heap.getOrElse(if (arch_64) default_heap * 2 else default_heap),
          max_heap = max_heap, more_settings = more_settings,
          more_preferences = more_preferences, verbose = verbose, build_tags = build_tags,
          build_args = build_args)

      if (output_file.isEmpty) {
        for ((_, log_path) <- results) Output.writeln(log_path.implode, stdout = true)
      }
      else {
        File.write(Path.explode(output_file),
          cat_lines(for ((_, log_path) <- results) yield log_path.implode))
      }

      val rc = Process_Result.RC.merge(results.map(p => p._1.rc))
      if (rc != Process_Result.RC.ok && exit_code) sys.exit(rc)
    }
  }



  /** remote build -- via rsync and ssh **/

  def remote_build(
    ssh: SSH.Session,
    isabelle_self: Path,
    isabelle_other: Path,
    isabelle_identifier: String = "remote_build_history",
    component_repository: String = Components.static_component_repository,
    components_base: String = Components.dynamic_components_base,
    clean_platform: Boolean = false,
    clean_archives: Boolean = false,
    shared_isabelle_self: Boolean = false,
    progress: Progress = new Progress,
    rev: String = "",
    afp_repos: Option[Path] = None,
    afp_rev: String = "",
    options: String = "",
    args: String = "",
    no_build: Boolean = false,
  ): List[(String, Bytes)] = {
    /* synchronize Isabelle + AFP repositories */

    def sync(target: Path, accurate: Boolean = false,
      rev: String = "", afp_rev: String = "", afp: Boolean = false
    ): Unit = {
      Sync.sync(ssh.options, Rsync.Context(progress = progress, ssh = ssh), target,
        thorough = accurate, preserve_jars = !accurate,
        rev = rev, dirs = Sync.afp_dirs(if (afp) afp_repos else None, rev = afp_rev))
    }

    if (!shared_isabelle_self) sync(isabelle_self)

    val self_isabelle =
      Other_Isabelle(isabelle_self, isabelle_identifier = isabelle_identifier,
        ssh = ssh, progress = progress)

    val clean_platforms = if (clean_platform) Some(List(ssh.isabelle_platform_family)) else None

    self_isabelle.init(fresh = !shared_isabelle_self, echo = true,
      component_repository = component_repository,
      other_settings = self_isabelle.init_components(components_base = components_base),
      clean_platforms = clean_platforms,
      clean_archives = clean_archives)

    sync(isabelle_other, accurate = true,
      rev = proper_string(rev) getOrElse "tip",
      afp_rev = proper_string(afp_rev) getOrElse "tip",
      afp = true)


    /* build */

    if (no_build) Nil
    else {
      ssh.with_tmp_dir { tmp_dir =>
        val output_file = tmp_dir + Path.explode("output")
        val build_options = if_proper(afp_repos, " -A") + " " + options
        try {
          val script =
            ssh.bash_path(Path.explode("Admin/build_other")) +
              " -R " + Bash.string(component_repository) +
              " -S " + Bash.string(components_base) +
              (clean_platforms match {
                case Some(ps) => " -O " + Bash.string(ps.mkString(","))
                case None => ""
              }) +
              (if (clean_archives) " -Q" else "") +
              " -o " + ssh.bash_path(output_file) + build_options + " " +
              ssh.bash_path(isabelle_other) + " " + args
          self_isabelle.bash(script, echo = true, strict = false).check
        }
        catch {
          case ERROR(msg) =>
            cat_error(msg, "The error(s) above occurred for Admin/build_other " + build_options)
        }

        for (line <- split_lines(ssh.read(output_file)))
        yield {
          val log = Path.explode(line)
          val bytes = ssh.read_bytes(log)
          ssh.delete(log)
          (log.file_name, bytes)
        }
      }
    }
  }
}
