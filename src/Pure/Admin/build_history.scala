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

  val BUILD_HISTORY = "build_history"
  val META_INFO_MARKER = "\fmeta_info = "


  /* augment settings */

  def augment_settings(
    other_isabelle: Other_Isabelle,
    threads: Int,
    arch_64: Boolean = false,
    heap: Int = default_heap,
    max_heap: Option[Int] = None,
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
  private val default_threads = 1
  private val default_heap = 1000
  private val default_isabelle_identifier = "build_history"

  def build_history(
    hg: Mercurial.Repository,
    progress: Progress = Ignore_Progress,
    rev: String = default_rev,
    isabelle_identifier: String = default_isabelle_identifier,
    components_base: String = "",
    fresh: Boolean = false,
    nonfree: Boolean = false,
    multicore_base: Boolean = false,
    threads_list: List[Int] = List(default_threads),
    arch_64: Boolean = false,
    heap: Int = default_heap,
    max_heap: Option[Int] = None,
    more_settings: List[String] = Nil,
    verbose: Boolean = false,
    build_args: List[String] = Nil): List[(Process_Result, Path)] =
  {
    /* sanity checks */

    if (File.eq(Path.explode("~~"), hg.root))
      error("Repository coincides with ISABELLE_HOME=" + Path.explode("~~").expand)

    for (threads <- threads_list if threads < 1) error("Bad threads value < 1: " + threads)

    if (heap < 100) error("Bad heap value < 100: " + heap)

    if (max_heap.isDefined && max_heap.get < heap)
      error("Bad max_heap value < heap: " + max_heap.get)

    System.getenv("ISABELLE_SETTINGS_PRESENT") match {
      case null | "" =>
      case _ => error("Cannot run build_history within existing Isabelle settings environment")
    }


    /* init repository */

    hg.update(rev = rev, clean = true)
    progress.echo_if(verbose, hg.log(rev, options = "-l1"))

    val isabelle_version = hg.id(rev)
    val other_isabelle = new Other_Isabelle(progress, hg.root, isabelle_identifier)


    /* main */

    val build_history_date = Date.now()
    val build_host = Isabelle_System.hostname()

    var first_build = true
    for (threads <- threads_list) yield
    {
      /* init settings */

      other_isabelle.init_settings(components_base, nonfree)
      other_isabelle.resolve_components(verbose)
      val ml_platform =
        augment_settings(other_isabelle, threads, arch_64, heap, max_heap, more_settings)

      val isabelle_output = Path.explode(other_isabelle("getenv -b ISABELLE_OUTPUT").check.out)
      val isabelle_output_log = isabelle_output + Path.explode("log")
      val isabelle_base_log = isabelle_output + Path.explode("../base_log")

      if (first_build) {
        other_isabelle.resolve_components(verbose)
        other_isabelle.bash(
          "env PATH=\"" + File.bash_path(Path.explode("~~/lib/dummy_stty").expand) + ":$PATH\" " +
            "bin/isabelle jedit -b" + (if (fresh) " -f" else ""),
          redirect = true, echo = verbose).check

        Isabelle_System.rm_tree(isabelle_base_log)
      }

      Isabelle_System.rm_tree(isabelle_output)
      Isabelle_System.mkdirs(isabelle_output)


      /* build */

      if (multicore_base && !first_build && isabelle_base_log.is_dir)
        Isabelle_System.copy_dir(isabelle_base_log, isabelle_output_log)

      val build_start = Date.now()
      val res =
        other_isabelle("build -v " + File.bash_args(build_args), redirect = true, echo = verbose)
      val build_end = Date.now()


      /* output log */

      val log_path =
        other_isabelle.isabelle_home_user +
          Build_Log.log_subdir(build_history_date) +
          Build_Log.log_filename(
            BUILD_HISTORY, build_history_date, build_host, ml_platform, "M" + threads).ext("gz")

      val build_info = Build_Log.Log_File(log_path.base.implode, res.out_lines).parse_build_info()

      val meta_info =
        List(Build_Log.Field.build_engine -> BUILD_HISTORY,
          Build_Log.Field.build_host -> build_host,
          Build_Log.Field.build_start -> Build_Log.print_date(build_start),
          Build_Log.Field.build_end -> Build_Log.print_date(build_end),
          Build_Log.Field.isabelle_version -> isabelle_version)

      val ml_statistics =
        build_info.finished_sessions.flatMap(session_name =>
          {
            val session_log = isabelle_output_log + Path.explode(session_name).ext("gz")
            if (session_log.is_file) {
              Build_Log.Log_File(session_log).parse_session_info(ml_statistics = true).
                ml_statistics.map(props => (Build_Log.SESSION_NAME -> session_name) :: props)
            }
            else Nil
          })

      val heap_sizes =
        build_info.finished_sessions.flatMap(session_name =>
          {
            val heap = isabelle_output + Path.explode(session_name)
            if (heap.is_file)
              Some("Heap " + session_name + " (" + Value.Long(heap.file.length) + " bytes)")
            else None
          })

      Isabelle_System.mkdirs(log_path.dir)
      File.write_gzip(log_path,
        terminate_lines(
          Build_Log.Log_File.print_props(META_INFO_MARKER, meta_info) :: res.out_lines :::
          ml_statistics.map(Build_Log.Log_File.print_props(Build_Log.ML_STATISTICS_MARKER, _)) :::
          heap_sizes))


      /* next build */

      if (multicore_base && first_build && isabelle_output_log.is_dir)
        Isabelle_System.copy_dir(isabelle_output_log, isabelle_base_log)

      first_build = false

      (res, log_path)
    }
  }


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool0 {
      var multicore_base = false
      var components_base = ""
      var heap: Option[Int] = None
      var max_heap: Option[Int] = None
      var threads_list = List(default_threads)
      var isabelle_identifier = default_isabelle_identifier
      var more_settings: List[String] = Nil
      var fresh = false
      var arch_64 = false
      var nonfree = false
      var rev = default_rev
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_history [OPTIONS] REPOSITORY [ARGS ...]

  Options are:
    -B           first multicore build serves as base for scheduling information
    -C DIR       base directory for Isabelle components (default: $ISABELLE_HOME_USER/../contrib)
    -H SIZE      minimal ML heap in MB (default: """ + default_heap + """ for x86, """ + default_heap * 2 + """ for x86_64)
    -M THREADS   multicore configurations (comma-separated list, default: """ + default_threads + """)
    -N NAME      alternative ISABELLE_IDENTIFIER (default: """ + default_isabelle_identifier + """)
    -U SIZE      maximal ML heap in MB (default: unbounded)
    -e TEXT      additional text for generated etc/settings
    -f           fresh build of Isabelle/Scala components (recommended)
    -m ARCH      processor architecture (32=x86, 64=x86_64, default: x86)
    -n           include nonfree components
    -r REV       update to revision (default: """ + default_rev + """)
    -v           verbose

  Build Isabelle sessions from the history of another REPOSITORY clone,
  passing ARGS directly to its isabelle build tool.
""",
        "B" -> (_ => multicore_base = true),
        "C:" -> (arg => components_base = arg),
        "H:" -> (arg => heap = Some(Value.Int.parse(arg))),
        "M:" -> (arg => threads_list = space_explode(',', arg).map(Value.Int.parse(_))),
        "N:" -> (arg => isabelle_identifier = arg),
        "U:" -> (arg => max_heap = Some(Value.Int.parse(arg))),
        "e:" -> (arg => more_settings = more_settings ::: List(arg)),
        "f" -> (_ => fresh = true),
        "m:" ->
          {
            case "32" | "x86" => arch_64 = false
            case "64" | "x86_64" => arch_64 = true
            case bad => error("Bad processor architecture: " + quote(bad))
          },
        "n" -> (_ => nonfree = true),
        "r:" -> (arg => rev = arg),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      val (root, build_args) =
        more_args match {
          case root :: build_args => (root, build_args)
          case _ => getopts.usage()
        }

      val hg = Mercurial.repository(Path.explode(root))
      val progress = new Console_Progress(stderr = true)
      val results =
        build_history(hg, progress = progress, rev = rev, isabelle_identifier = isabelle_identifier,
          components_base = components_base, fresh = fresh, nonfree = nonfree,
          multicore_base = multicore_base, threads_list = threads_list, arch_64 = arch_64,
          heap = heap.getOrElse(if (arch_64) default_heap * 2 else default_heap),
          max_heap = max_heap, more_settings = more_settings, verbose = verbose,
          build_args = build_args)

      for ((_, log_path) <- results)
        Output.writeln(log_path.implode, stdout = true)

      val rc = (0 /: results) { case (rc, (res, _)) => rc max res.rc }
      if (rc != 0) sys.exit(rc)
    }
  }



  /** remote build_history -- via command-line **/

  def remote_build_history(
    session: SSH.Session,
    isabelle_repos_self: Path,
    isabelle_repos_other: Path,
    isabelle_repos_source: String = "http://isabelle.in.tum.de/repos/isabelle",
    self_update: Boolean = false,
    progress: Progress = Ignore_Progress,
    options: String = "",
    args: String = ""): List[(String, Bytes)] =
  {
    using(session.sftp())(sftp =>
      {
        val isabelle_admin = sftp.remote_path(isabelle_repos_self + Path.explode("Admin"))


        /* prepare repository clones */

        val isabelle_hg =
          Mercurial.setup_repository(
            isabelle_repos_source, isabelle_repos_self, ssh = Some(session))

        if (self_update) {
          isabelle_hg.pull()
          isabelle_hg.update(clean = true)
          session.execute(File.bash_string(isabelle_admin + "/build") + " jars_fresh").check
        }

        Mercurial.setup_repository(
          sftp.remote_path(isabelle_repos_self), isabelle_repos_other, ssh = Some(session))


        /* Admin/build_history */

        val result =
          session.execute(
            File.bash_string(isabelle_admin + "/build_history") + " " + options + " " +
              File.bash_string(sftp.remote_path(isabelle_repos_other)) + " " + args,
            progress_stderr = progress.echo(_)).check

        for (line <- result.out_lines; log = Path.explode(line))
          yield (log.base.implode, sftp.read_bytes(log))
      })
  }
}
