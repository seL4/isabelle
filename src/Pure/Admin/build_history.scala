/*  Title:      Pure/Admin/build_history.scala
    Author:     Makarius

Build other history versions.
*/

package isabelle


object Build_History
{
  /* log files */

  val engine = "build_history"
  val log_prefix = engine + "_"


  /* augment settings */

  def augment_settings(
    other_isabelle: Other_Isabelle,
    threads: Int,
    arch_64: Boolean,
    heap: Int,
    max_heap: Option[Int],
    more_settings: List[String]): String =
  {
    val (ml_platform, ml_settings) =
    {
      val cygwin_32 = "x86-cygwin"
      val windows_32 = "x86-windows"
      val windows_64 = "x86_64-windows"
      val windows_64_32 = "x86_64_32-windows"
      val platform_32 = other_isabelle.getenv("ISABELLE_PLATFORM32")
      val platform_64 = other_isabelle.getenv("ISABELLE_PLATFORM64")
      val platform_64_32 = platform_64.replace("x86_64-", "x86_64_32-")

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



  /** build_history **/

  private val default_user_home = Path.USER_HOME
  private val default_rev = "tip"
  private val default_multicore = (1, 1)
  private val default_heap = 1500
  private val default_isabelle_identifier = "build_history"

  def build_history(
    options: Options,
    root: Path,
    user_home: Path = default_user_home,
    progress: Progress = new Progress,
    rev: String = default_rev,
    afp_rev: Option[String] = None,
    afp_partition: Int = 0,
    isabelle_identifier: String = default_isabelle_identifier,
    ml_statistics_step: Int = 1,
    component_repository: String = Components.default_component_repository,
    components_base: Path = Components.default_components_base,
    fresh: Boolean = false,
    hostname: String = "",
    multicore_base: Boolean = false,
    multicore_list: List[(Int, Int)] = List(default_multicore),
    arch_64: Boolean = false,
    heap: Int = default_heap,
    max_heap: Option[Int] = None,
    init_settings: List[String] = Nil,
    more_settings: List[String] = Nil,
    more_preferences: List[String] = Nil,
    verbose: Boolean = false,
    build_tags: List[String] = Nil,
    build_args: List[String] = Nil): List[(Process_Result, Path)] =
  {
    /* sanity checks */

    if (File.eq(Path.ISABELLE_HOME, root))
      error("Repository coincides with ISABELLE_HOME=" + Path.ISABELLE_HOME.expand)

    for ((threads, _) <- multicore_list if threads < 1)
      error("Bad threads value < 1: " + threads)
    for ((_, processes) <- multicore_list if processes < 1)
      error("Bad processes value < 1: " + processes)

    if (heap < 100) error("Bad heap value < 100: " + heap)

    if (max_heap.isDefined && max_heap.get < heap)
      error("Bad max_heap value < heap: " + max_heap.get)

    System.getenv("ISABELLE_SETTINGS_PRESENT") match {
      case null | "" =>
      case _ => error("Cannot run build_history within existing Isabelle settings environment")
    }


    /* checkout Isabelle + AFP repository */

    def checkout(dir: Path, version: String): String =
    {
      val hg = Mercurial.repository(dir)
      hg.update(rev = version, clean = true)
      progress.echo_if(verbose, hg.log(version, options = "-l1"))
      hg.id(rev = version)
    }

    val isabelle_version = checkout(root, rev)

    val afp_repos = root + Path.explode("AFP")
    val afp_version = afp_rev.map(checkout(afp_repos, _))

    val (afp_build_args, afp_sessions) =
      if (afp_rev.isEmpty) (Nil, Nil)
      else {
        val (opt, sessions) = {
          if (afp_partition == 0) ("-d", Nil)
          else {
            try {
              val afp = AFP.init(options, afp_repos)
              ("-d", afp.partition(afp_partition))
            } catch { case ERROR(_) => ("-D", Nil) }
          }
        }
        (List(opt, "~~/AFP/thys"), sessions)
      }


    /* main */

    val other_isabelle =
      Other_Isabelle(root, isabelle_identifier = isabelle_identifier,
        user_home = user_home, progress = progress)

    val build_host = proper_string(hostname) getOrElse Isabelle_System.hostname()
    val build_history_date = Date.now()
    val build_group_id = build_host + ":" + build_history_date.time.ms

    var first_build = true
    for ((threads, processes) <- multicore_list) yield
    {
      /* init settings */

      val component_settings =
        other_isabelle.init_components(
          component_repository = component_repository,
          components_base = components_base,
          catalogs = List("main", "optional"))
      other_isabelle.init_settings(component_settings ::: init_settings)
      other_isabelle.resolve_components(echo = verbose)
      val ml_platform =
        augment_settings(other_isabelle, threads, arch_64, heap, max_heap, more_settings)

      File.write(other_isabelle.etc_preferences, cat_lines(more_preferences))

      val isabelle_output =
        other_isabelle.isabelle_home_user + Path.explode("heaps") +
          Path.explode(other_isabelle.getenv("ML_IDENTIFIER"))
      val isabelle_output_log = isabelle_output + Path.explode("log")
      val isabelle_base_log = isabelle_output + Path.explode("../base_log")

      if (first_build) {
        other_isabelle.resolve_components(echo = verbose)

        if (fresh)
          Isabelle_System.rm_tree(other_isabelle.isabelle_home + Path.explode("lib/classes"))
        other_isabelle.bash(
          "env PATH=\"" + File.bash_path(Path.explode("~~/lib/dummy_stty").expand) + ":$PATH\" " +
            "bin/isabelle jedit -b", redirect = true, echo = verbose).check

        for {
          tool <- List("ghc_setup", "ocaml_setup")
          if other_isabelle.getenv("ISABELLE_" + Word.uppercase(tool)) == "true" &&
            (other_isabelle.isabelle_home + Path.explode("lib/Tools/" + tool)).is_file
        } other_isabelle(tool, echo = verbose)

        Isabelle_System.rm_tree(isabelle_base_log)
      }

      Isabelle_System.rm_tree(isabelle_output)
      Isabelle_System.make_directory(isabelle_output)

      val log_path =
        other_isabelle.isabelle_home_user +
          Build_Log.log_subdir(build_history_date) +
          Build_Log.log_filename(Build_History.engine, build_history_date,
            List(build_host, ml_platform, "M" + threads) ::: build_tags)

      Isabelle_System.make_directory(log_path.dir)

      val build_out = other_isabelle.isabelle_home_user + Path.explode("log/build.out")
      val build_out_progress = new File_Progress(build_out)
      build_out.file.delete


      /* build */

      if (multicore_base && !first_build && isabelle_base_log.is_dir)
        Isabelle_System.copy_dir(isabelle_base_log, isabelle_output_log)

      val build_start = Date.now()
      val build_args1 = List("-v", "-j" + processes) ::: afp_build_args ::: build_args

      val build_isabelle =
        Other_Isabelle(root, isabelle_identifier = isabelle_identifier,
          user_home = user_home, progress = build_out_progress)
      val build_result =
        build_isabelle("build " + Bash.strings(build_args1 ::: afp_sessions),
          redirect = true, echo = true, strict = false)

      val build_end = Date.now()

      val build_info: Build_Log.Build_Info =
        Build_Log.Log_File(log_path.file_name, build_result.out_lines).
          parse_build_info(ml_statistics = true)


      /* output log */

      val store = Sessions.store(options + "build_database_server=false")

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
          Build_Log.Prop.isabelle_version.name -> isabelle_version) :::
        afp_version.map(Build_Log.Prop.afp_version.name -> _).toList

      build_out_progress.echo("Reading session build info ...")
      val session_build_info =
        build_info.finished_sessions.flatMap(session_name =>
          {
            val database = isabelle_output + store.database(session_name)

            if (database.is_file) {
              using(SQLite.open_database(database))(db =>
              {
                val theory_timings =
                  try {
                    store.read_theory_timings(db, session_name).map(ps =>
                      Protocol.Theory_Timing_Marker((Build_Log.SESSION_NAME, session_name) :: ps))
                  }
                  catch { case ERROR(_) => Nil }

                val session_sources =
                  store.read_build(db, session_name).map(_.sources) match {
                    case Some(sources) if sources.length == SHA1.digest_length =>
                      List("Sources " + session_name + " " + sources)
                    case _ => Nil
                  }

                theory_timings ::: session_sources
              })
            }
            else Nil
          })

      build_out_progress.echo("Reading ML statistics ...")
      val ml_statistics =
        build_info.finished_sessions.flatMap(session_name =>
          {
            val database = isabelle_output + store.database(session_name)
            val log_gz = isabelle_output + store.log_gz(session_name)

            val properties =
              if (database.is_file) {
                using(SQLite.open_database(database))(db =>
                  store.read_ml_statistics(db, session_name))
              }
              else if (log_gz.is_file) {
                Build_Log.Log_File(log_gz).parse_session_info(ml_statistics = true).ml_statistics
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
          })

      build_out_progress.echo("Reading error messages ...")
      val session_errors =
        build_info.failed_sessions.flatMap(session_name =>
          {
            val database = isabelle_output + store.database(session_name)
            val errors =
              if (database.is_file) {
                try {
                  using(SQLite.open_database(database))(db => store.read_errors(db, session_name))
                } // column "errors" could be missing
                catch { case _: java.sql.SQLException => Nil }
              }
              else Nil
            errors.map(msg => List(Build_Log.SESSION_NAME -> session_name, Markup.CONTENT -> msg))
          })

      build_out_progress.echo("Reading heap sizes ...")
      val heap_sizes =
        build_info.finished_sessions.flatMap(session_name =>
          {
            val heap = isabelle_output + Path.explode(session_name)
            if (heap.is_file)
              Some("Heap " + session_name + " (" + Value.Long(heap.file.length) + " bytes)")
            else None
          })

      build_out_progress.echo("Writing log file " + log_path.xz + " ...")
      File.write_xz(log_path.xz,
        terminate_lines(
          Protocol.Meta_Info_Marker(meta_info) :: build_result.out_lines :::
          session_build_info :::
          ml_statistics.map(Protocol.ML_Statistics_Marker.apply) :::
          session_errors.map(Protocol.Error_Message_Marker.apply) :::
          heap_sizes), XZ.options(6))


      /* next build */

      if (multicore_base && first_build && isabelle_output_log.is_dir)
        Isabelle_System.copy_dir(isabelle_output_log, isabelle_base_log)

      Isabelle_System.rm_tree(isabelle_output)

      first_build = false

      (build_result, log_path.xz)
    }
  }


  /* command line entry point */

  private object Multicore
  {
    private val Pat1 = """^(\d+)$""".r
    private val Pat2 = """^(\d+)x(\d+)$""".r

    def parse(s: String): (Int, Int) =
      s match {
        case Pat1(Value.Int(x)) => (x, 1)
        case Pat2(Value.Int(x), Value.Int(y)) => (x, y)
        case _ => error("Bad multicore configuration: " + quote(s))
      }
  }

  def main(args: Array[String]): Unit =
  {
    Command_Line.tool {
      var afp_rev: Option[String] = None
      var multicore_base = false
      var components_base: Path = Components.default_components_base
      var heap: Option[Int] = None
      var max_heap: Option[Int] = None
      var multicore_list = List(default_multicore)
      var isabelle_identifier = default_isabelle_identifier
      var afp_partition = 0
      var component_repository = Components.default_component_repository
      var more_settings: List[String] = Nil
      var more_preferences: List[String] = Nil
      var fresh = false
      var hostname = ""
      var init_settings: List[String] = Nil
      var arch_64 = false
      var output_file = ""
      var rev = default_rev
      var ml_statistics_step = 1
      var build_tags = List.empty[String]
      var user_home = default_user_home
      var verbose = false
      var exit_code = false

      val getopts = Getopts("""
Usage: Admin/build_history [OPTIONS] REPOSITORY [ARGS ...]

  Options are:
    -A REV       include $ISABELLE_HOME/AFP repository at given revision
    -B           first multicore build serves as base for scheduling information
    -C DIR       base directory for Isabelle components (default: """ +
      Components.default_components_base + """)
    -H SIZE      minimal ML heap in MB (default: """ + default_heap + """ for x86, """ +
      default_heap * 2 + """ for x86_64)
    -M MULTICORE multicore configurations (see below)
    -N NAME      alternative ISABELLE_IDENTIFIER (default: """ + default_isabelle_identifier + """)
    -P NUMBER    AFP partition number (0, 1, 2, default: 0=unrestricted)
    -R URL       remote repository for Isabelle components (default: """ +
      Components.default_component_repository + """)
    -U SIZE      maximal ML heap in MB (default: unbounded)
    -e TEXT      additional text for generated etc/settings
    -f           fresh build of Isabelle/Scala components (recommended)
    -h NAME      override local hostname
    -i TEXT      initial text for generated etc/settings
    -m ARCH      processor architecture (32=x86, 64=x86_64, default: x86)
    -o FILE      output file for log names (default: stdout)
    -p TEXT      additional text for generated etc/preferences
    -r REV       update to revision (default: """ + default_rev + """)
    -s NUMBER    step size for ML statistics (0=none, 1=all, n=step, default: 1)
    -t TAG       free-form build tag (multiple occurrences possible)
    -u DIR       alternative USER_HOME directory
    -v           verbose
    -x           return overall exit code from build processes

  Build Isabelle sessions from the history of another REPOSITORY clone,
  passing ARGS directly to its isabelle build tool.

  Each MULTICORE configuration consists of one or two numbers (default 1):
  THREADS or THREADSxPROCESSES, e.g. -M 1,2,4 or -M 1x4,2x2,4.
""",
        "A:" -> (arg => afp_rev = Some(arg)),
        "B" -> (_ => multicore_base = true),
        "C:" -> (arg => components_base = Path.explode(arg)),
        "H:" -> (arg => heap = Some(Value.Int.parse(arg))),
        "M:" -> (arg => multicore_list = space_explode(',', arg).map(Multicore.parse)),
        "N:" -> (arg => isabelle_identifier = arg),
        "P:" -> (arg => afp_partition = Value.Int.parse(arg)),
        "R:" -> (arg => component_repository = arg),
        "U:" -> (arg => max_heap = Some(Value.Int.parse(arg))),
        "e:" -> (arg => more_settings = more_settings ::: List(arg)),
        "f" -> (_ => fresh = true),
        "h:" -> (arg => hostname = arg),
        "i:" -> (arg => init_settings = init_settings ::: List(arg)),
        "m:" ->
          {
            case "32" | "x86" => arch_64 = false
            case "64" | "x86_64" => arch_64 = true
            case bad => error("Bad processor architecture: " + quote(bad))
          },
        "o:" -> (arg => output_file = arg),
        "p:" -> (arg => more_preferences = more_preferences ::: List(arg)),
        "r:" -> (arg => rev = arg),
        "s:" -> (arg => ml_statistics_step = Value.Int.parse(arg)),
        "t:" -> (arg => build_tags = build_tags ::: List(arg)),
        "u:" -> (arg => user_home = Path.explode(arg)),
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
        build_history(Options.init(), root, user_home = user_home, progress = progress, rev = rev,
          afp_rev = afp_rev, afp_partition = afp_partition,
          isabelle_identifier = isabelle_identifier, ml_statistics_step = ml_statistics_step,
          component_repository = component_repository, components_base = components_base,
          fresh = fresh, hostname = hostname, multicore_base = multicore_base,
          multicore_list = multicore_list, arch_64 = arch_64,
          heap = heap.getOrElse(if (arch_64) default_heap * 2 else default_heap),
          max_heap = max_heap, init_settings = init_settings, more_settings = more_settings,
          more_preferences = more_preferences, verbose = verbose, build_tags = build_tags,
          build_args = build_args)

      if (output_file == "") {
        for ((_, log_path) <- results)
          Output.writeln(log_path.implode, stdout = true)
      }
      else {
        File.write(Path.explode(output_file),
          cat_lines(for ((_, log_path) <- results) yield log_path.implode))
      }

      val rc = results.foldLeft(0) { case (rc, (res, _)) => rc max res.rc }
      if (rc != 0 && exit_code) sys.exit(rc)
    }
  }



  /** remote build_history -- via command-line **/

  def remote_build_history(
    ssh: SSH.Session,
    isabelle_repos_self: Path,
    isabelle_repos_other: Path,
    isabelle_repository: Mercurial.Server = Isabelle_System.isabelle_repository,
    afp_repository: Mercurial.Server = Isabelle_System.afp_repository,
    isabelle_identifier: String = "remote_build_history",
    self_update: Boolean = false,
    progress: Progress = new Progress,
    rev: String = "",
    afp_rev: Option[String] = None,
    options: String = "",
    args: String = ""): List[(String, Bytes)] =
  {
    /* Isabelle self repository */

    val self_hg =
      Mercurial.setup_repository(isabelle_repository.root, isabelle_repos_self, ssh = ssh)

    def execute(cmd: String, args: String, echo: Boolean = false, strict: Boolean = true): Unit =
      ssh.execute(
        Isabelle_System.export_isabelle_identifier(isabelle_identifier) +
          ssh.bash_path(isabelle_repos_self + Path.explode(cmd)) + " " + args,
        progress_stdout = progress.echo_if(echo, _),
        progress_stderr = progress.echo_if(echo, _),
        strict = strict).check

    if (self_update) {
      val hg = Mercurial.repository(Path.ISABELLE_HOME)
      hg.push(self_hg.root_url, force = true)
      self_hg.update(rev = hg.parent(), clean = true)

      execute("bin/isabelle", "components -I")
      execute("bin/isabelle", "components -a", echo = true)
      execute("bin/isabelle", "jedit -bf")
    }

    val rev_id = self_hg.id(rev)


    /* Isabelle other + AFP repository */

    if (Mercurial.is_repository(isabelle_repos_other, ssh = ssh)) {
      ssh.rm_tree(isabelle_repos_other)
    }

    Mercurial.clone_repository(
      ssh.bash_path(isabelle_repos_self), isabelle_repos_other, rev = rev_id, ssh = ssh)

    val afp_options =
      if (afp_rev.isEmpty) ""
      else {
        val afp_repos = isabelle_repos_other + Path.explode("AFP")
        Mercurial.setup_repository(afp_repository.root, afp_repos, ssh = ssh)
        " -A " + Bash.string(afp_rev.get)
      }


    /* Admin/build_history */

    ssh.with_tmp_dir(tmp_dir =>
    {
      val output_file = tmp_dir + Path.explode("output")

      val rev_options = if (rev == "") "" else " -r " + Bash.string(rev_id)

      try {
        execute("Admin/build_history",
          "-o " + ssh.bash_path(output_file) + rev_options + afp_options + " " + options + " " +
            ssh.bash_path(isabelle_repos_other) + " " + args,
          echo = true, strict = false)
      }
      catch {
        case ERROR(msg) =>
          cat_error(msg,
            "The error(s) above occurred for build_bistory " + rev_options + afp_options)
      }

      for (line <- split_lines(ssh.read(output_file)))
      yield {
        val log = Path.explode(line)
        val bytes = ssh.read_bytes(log)
        ssh.rm(log)
        (log.file_name, bytes)
      }
    })
  }
}
