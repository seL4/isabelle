/*  Title:      Pure/Admin/build_history.scala
    Author:     Makarius

Build other history versions.
*/

package isabelle


import java.io.{File => JFile}
import java.time.format.DateTimeFormatter
import java.util.Locale


object Build_History
{
  /* log files */

  val engine = "build_history"
  val log_prefix = engine + "_"
  val META_INFO_MARKER = "\fmeta_info = "


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
      val windows_32 = "x86-windows"
      val windows_64 = "x86_64-windows"
      val platform_32 = other_isabelle("getenv -b ISABELLE_PLATFORM32").check.out
      val platform_64 = other_isabelle("getenv -b ISABELLE_PLATFORM64").check.out
      val platform_family = other_isabelle("getenv -b ISABELLE_PLATFORM_FAMILY").check.out

      val polyml_home =
        try { Path.explode(other_isabelle("getenv -b ML_HOME").check.out).dir }
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
          if (check_dir(windows_32)) windows_32
          else platform_32  // x86-cygwin
        }
        else {
          val (platform, platform_name) =
            if (arch_64) (platform_64, "x86_64-" + platform_family)
            else (platform_32, "x86-" + platform_family)
          if (check_dir(platform)) platform else err(platform_name)
        }

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

  private val default_rev = "tip"
  private val default_multicore = (1, 1)
  private val default_heap = 1500
  private val default_isabelle_identifier = "build_history"

  def build_history(
    options: Options,
    root: Path,
    progress: Progress = No_Progress,
    rev: String = default_rev,
    afp_rev: Option[String] = None,
    afp_partition: Int = 0,
    isabelle_identifier: String = default_isabelle_identifier,
    ml_statistics_step: Int = 1,
    components_base: String = "",
    fresh: Boolean = false,
    nonfree: Boolean = false,
    multicore_base: Boolean = false,
    multicore_list: List[(Int, Int)] = List(default_multicore),
    arch_64: Boolean = false,
    heap: Int = default_heap,
    max_heap: Option[Int] = None,
    init_settings: List[String] = Nil,
    more_settings: List[String] = Nil,
    verbose: Boolean = false,
    build_tags: List[String] = Nil,
    build_args: List[String] = Nil): List[(Process_Result, Path)] =
  {
    /* sanity checks */

    if (File.eq(Path.explode("~~"), root))
      error("Repository coincides with ISABELLE_HOME=" + Path.explode("~~").expand)

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
        val afp = AFP.init(options, afp_repos)
        (List("-d", "~~/AFP/thys"), afp.partition(afp_partition))
      }


    /* main */

    val other_isabelle = new Other_Isabelle(progress, root, isabelle_identifier)

    val build_host = Isabelle_System.hostname()
    val build_history_date = Date.now()
    val build_group_id = build_host + ":" + build_history_date.time.ms

    var first_build = true
    for ((threads, processes) <- multicore_list) yield
    {
      /* init settings */

      other_isabelle.init_settings(components_base, nonfree, init_settings)
      other_isabelle.resolve_components(verbose)
      val ml_platform =
        augment_settings(other_isabelle, threads, arch_64, heap, max_heap, more_settings)

      val isabelle_output = Path.explode(other_isabelle("getenv -b ISABELLE_OUTPUT").check.out)
      val isabelle_output_log = isabelle_output + Path.explode("log")
      val isabelle_base_log = isabelle_output + Path.explode("../base_log")

      if (first_build) {
        other_isabelle.resolve_components(verbose)

        if (fresh)
          Isabelle_System.rm_tree(other_isabelle.isabelle_home + Path.explode("lib/classes"))
        other_isabelle.bash(
          "env PATH=\"" + File.bash_path(Path.explode("~~/lib/dummy_stty").expand) + ":$PATH\" " +
            "bin/isabelle jedit -b", redirect = true, echo = verbose).check

        Isabelle_System.rm_tree(isabelle_base_log)
      }

      Isabelle_System.rm_tree(isabelle_output)
      Isabelle_System.mkdirs(isabelle_output)

      val log_path =
        other_isabelle.isabelle_home_user +
          Build_Log.log_subdir(build_history_date) +
          Build_Log.log_filename(Build_History.engine, build_history_date,
            List(build_host, ml_platform, "M" + threads) ::: build_tags)

      Isabelle_System.mkdirs(log_path.dir)

      val build_out = other_isabelle.isabelle_home_user + Path.explode("log/build.out")
      val build_out_progress = new File_Progress(build_out)
      build_out.file.delete


      /* build */

      if (multicore_base && !first_build && isabelle_base_log.is_dir)
        Isabelle_System.copy_dir(isabelle_base_log, isabelle_output_log)

      val build_start = Date.now()
      val build_args1 = List("-v", "-j" + processes) ::: afp_build_args ::: build_args
      val build_result =
        (new Other_Isabelle(build_out_progress, root, isabelle_identifier))(
          "build " + Bash.strings(build_args1 ::: afp_sessions), redirect = true, echo = true,
          strict = false)
      val build_end = Date.now()

      val build_info: Build_Log.Build_Info =
        Build_Log.Log_File(log_path.base_name, build_result.out_lines).
          parse_build_info(ml_statistics = true)


      /* output log */

      val store = Sessions.store()

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

      build_out_progress.echo("Writing log file " + log_path.ext("xz") + " ...")
      File.write_xz(log_path.ext("xz"),
        terminate_lines(
          Build_Log.Log_File.print_props(META_INFO_MARKER, meta_info) :: build_result.out_lines :::
          ml_statistics.map(Build_Log.Log_File.print_props(Build_Log.ML_STATISTICS_MARKER, _)) :::
          session_errors.map(Build_Log.Log_File.print_props(Build_Log.ERROR_MESSAGE_MARKER, _)) :::
          heap_sizes), XZ.options(6))


      /* next build */

      if (multicore_base && first_build && isabelle_output_log.is_dir)
        Isabelle_System.copy_dir(isabelle_output_log, isabelle_base_log)

      Isabelle_System.rm_tree(isabelle_output)

      first_build = false

      (build_result, log_path.ext("xz"))
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

  def main(args: Array[String])
  {
    Command_Line.tool0 {
      var afp_rev: Option[String] = None
      var multicore_base = false
      var components_base = ""
      var heap: Option[Int] = None
      var max_heap: Option[Int] = None
      var multicore_list = List(default_multicore)
      var isabelle_identifier = default_isabelle_identifier
      var afp_partition = 0
      var more_settings: List[String] = Nil
      var fresh = false
      var init_settings: List[String] = Nil
      var arch_64 = false
      var nonfree = false
      var output_file = ""
      var rev = default_rev
      var ml_statistics_step = 1
      var build_tags = List.empty[String]
      var verbose = false
      var exit_code = false

      val getopts = Getopts("""
Usage: isabelle build_history [OPTIONS] REPOSITORY [ARGS ...]

  Options are:
    -A REV       include $ISABELLE_HOME/AFP repository at given revision
    -B           first multicore build serves as base for scheduling information
    -C DIR       base directory for Isabelle components (default: $ISABELLE_HOME_USER/../contrib)
    -H SIZE      minimal ML heap in MB (default: """ + default_heap + """ for x86, """ +
      default_heap * 2 + """ for x86_64)
    -M MULTICORE multicore configurations (see below)
    -N NAME      alternative ISABELLE_IDENTIFIER (default: """ + default_isabelle_identifier + """)
    -P NUMBER    AFP partition number (0, 1, 2, default: 0=unrestricted)
    -U SIZE      maximal ML heap in MB (default: unbounded)
    -e TEXT      additional text for generated etc/settings
    -f           fresh build of Isabelle/Scala components (recommended)
    -i TEXT      initial text for generated etc/settings
    -m ARCH      processor architecture (32=x86, 64=x86_64, default: x86)
    -n           include nonfree components
    -o FILE      output file for log names (default: stdout)
    -r REV       update to revision (default: """ + default_rev + """)
    -s NUMBER    step size for ML statistics (0=none, 1=all, n=step, default: 1)
    -t TAG       free-form build tag (multiple occurrences possible)
    -v           verbose
    -x           return overall exit code from build processes

  Build Isabelle sessions from the history of another REPOSITORY clone,
  passing ARGS directly to its isabelle build tool.

  Each MULTICORE configuration consists of one or two numbers (default 1):
  THREADS or THREADSxPROCESSES, e.g. -M 1,2,4 or -M 1x4,2x2,4.
""",
        "A:" -> (arg => afp_rev = Some(arg)),
        "B" -> (_ => multicore_base = true),
        "C:" -> (arg => components_base = arg),
        "H:" -> (arg => heap = Some(Value.Int.parse(arg))),
        "M:" -> (arg => multicore_list = space_explode(',', arg).map(Multicore.parse(_))),
        "N:" -> (arg => isabelle_identifier = arg),
        "P:" -> (arg => afp_partition = Value.Int.parse(arg)),
        "U:" -> (arg => max_heap = Some(Value.Int.parse(arg))),
        "e:" -> (arg => more_settings = more_settings ::: List(arg)),
        "f" -> (_ => fresh = true),
        "i:" -> (arg => init_settings = init_settings ::: List(arg)),
        "m:" ->
          {
            case "32" | "x86" => arch_64 = false
            case "64" | "x86_64" => arch_64 = true
            case bad => error("Bad processor architecture: " + quote(bad))
          },
        "n" -> (_ => nonfree = true),
        "o:" -> (arg => output_file = arg),
        "r:" -> (arg => rev = arg),
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
        build_history(Options.init(), root, progress = progress, rev = rev, afp_rev = afp_rev,
          afp_partition = afp_partition, isabelle_identifier = isabelle_identifier,
          ml_statistics_step = ml_statistics_step, components_base = components_base, fresh = fresh,
          nonfree = nonfree, multicore_base = multicore_base, multicore_list = multicore_list,
          arch_64 = arch_64, heap = heap.getOrElse(if (arch_64) default_heap * 2 else default_heap),
          max_heap = max_heap, init_settings = init_settings, more_settings = more_settings,
          verbose = verbose, build_tags = build_tags, build_args = build_args)

      if (output_file == "") {
        for ((_, log_path) <- results)
          Output.writeln(log_path.implode, stdout = true)
      }
      else {
        File.write(Path.explode(output_file),
          cat_lines(for ((_, log_path) <- results) yield log_path.implode))
      }

      val rc = (0 /: results) { case (rc, (res, _)) => rc max res.rc }
      if (rc != 0 && exit_code) sys.exit(rc)
    }
  }



  /** remote build_history -- via command-line **/

  def remote_build_history(
    ssh: SSH.Session,
    isabelle_repos_self: Path,
    isabelle_repos_other: Path,
    isabelle_repos_source: String = "http://isabelle.in.tum.de/repos/isabelle",
    afp_repos_source: String = AFP.repos_source,
    isabelle_identifier: String = "remote_build_history",
    self_update: Boolean = false,
    push_isabelle_home: Boolean = false,
    progress: Progress = No_Progress,
    rev: String = "",
    afp_rev: Option[String] = None,
    options: String = "",
    args: String = ""): List[(String, Bytes)] =
  {
    /* Isabelle self repository */

    val isabelle_admin = isabelle_repos_self + Path.explode("Admin")

    val isabelle_hg =
      Mercurial.setup_repository(isabelle_repos_source, isabelle_repos_self, ssh = ssh)

    if (self_update) {
      val self_rev =
        if (push_isabelle_home) {
          val isabelle_home_hg = Mercurial.repository(Path.explode("~~"))
          val self_rev = isabelle_home_hg.id()
          isabelle_home_hg.push(isabelle_hg.root_url, rev = self_rev, force = true)
          self_rev
        }
        else {
          isabelle_hg.pull()
          isabelle_hg.id()
        }
      isabelle_hg.update(rev = self_rev, clean = true)
      for (cmd <- List("components -I", "components -a")) {
        ssh.execute(
          ssh.bash_path(isabelle_repos_self + Path.explode("bin/isabelle")) + " " + cmd).check
      }
      ssh.execute(ssh.bash_path(isabelle_admin + Path.explode("build")) + " jars_fresh").check
    }


    /* Isabelle other + AFP repository */

    if (Mercurial.is_repository(isabelle_repos_other, ssh = ssh)) {
      ssh.rm_tree(isabelle_repos_other)
    }
    val other_hg =
      Mercurial.clone_repository(
        ssh.bash_path(isabelle_repos_self), isabelle_repos_other, rev = rev, ssh = ssh)

    val afp_options =
      if (afp_rev.isEmpty) ""
      else {
        val afp_repos = isabelle_repos_other + Path.explode("AFP")
        val afp_hg = Mercurial.setup_repository(afp_repos_source, afp_repos, ssh = ssh)
        " -A " + Bash.string(afp_rev.get)
      }


    /* Admin/build_history */

    ssh.with_tmp_dir(tmp_dir =>
    {
      val output_file = tmp_dir + Path.explode("output")

      ssh.execute(
        Isabelle_System.export_isabelle_identifier(isabelle_identifier) +
        ssh.bash_path(isabelle_admin + Path.explode("build_history")) +
          " -o " + ssh.bash_path(output_file) +
          (if (rev == "") "" else " -r " + Bash.string(rev)) + " " +
          options + afp_options + " " + ssh.bash_path(isabelle_repos_other) + " " + args,
        progress_stdout = progress.echo(_),
        progress_stderr = progress.echo(_),
        strict = false).check

      for (line <- split_lines(ssh.read(output_file)))
      yield {
        val log = Path.explode(line)
        val bytes = ssh.read_bytes(log)
        ssh.rm(log)
        (log.base_name, bytes)
      }
    })
  }
}
