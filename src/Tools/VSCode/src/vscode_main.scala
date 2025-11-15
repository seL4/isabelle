/*  Title:      Tools/VSCode/src/vscode_main.scala
    Author:     Makarius

Main application entry point for Isabelle/VSCode.
*/

package isabelle.vscode


import isabelle._

import java.util.zip.ZipFile
import java.io.{PrintStream, OutputStream}

import scala.collection.mutable


object VSCode_Main {
  /* vscodium command-line interface */

  def server_log_path: Path =
    Path.explode("$ISABELLE_VSCODE_SETTINGS/server.log").expand

  def default_java_options: String =
    Isabelle_System.getenv("VSCODE_JAVA_OPTIONS")

  def run_vscodium(args: List[String],
    environment: List[(String, String)] = Nil,
    options: List[String] = Nil,
    java_options: String = default_java_options,
    logic: String = Isabelle_System.default_logic(),
    logic_ancestor: String = "",
    logic_requirements: Boolean = false,
    session_dirs: List[Path] = Nil,
    include_sessions: List[String] = Nil,
    modes: List[String] = Nil,
    no_build: Boolean = false,
    server_log: Boolean = false,
    verbose: Boolean = false,
    background: Boolean = false,
    progress: Progress = new Progress
  ): Process_Result = {
    def platform_path(s: String): String = File.platform_path(Path.explode(s))

    val args_json =
      JSON.optional("options" -> proper_list(options)) ++
      JSON.optional("logic" -> proper_string(logic)) ++
      JSON.optional("logic_ancestor" -> proper_string(logic_ancestor)) ++
      JSON.optional("logic_requirements" -> proper_bool(logic_requirements)) ++
      JSON.optional("session_dirs" ->
        proper_list(session_dirs.map(dir => Sessions.check_session_dir(dir).absolute.implode))) ++
      JSON.optional("include_sessions" -> proper_list(include_sessions)) ++
      JSON.optional("modes" -> proper_list(modes)) ++
      JSON.optional("no_build" -> proper_bool(no_build)) ++
      JSON.optional("log_file" ->
        (if (server_log) Some(server_log_path.absolute.implode) else None)) ++
      JSON.optional("verbose" -> proper_bool(verbose))

    val env =
      Isabelle_System.Settings.env(environment ::: List(
        "ISABELLE_TOOL_JAVA_OPTIONS" -> java_options,
        "ISABELLE_VSCODIUM_ARGS" -> JSON.Format(args_json),
        "ISABELLE_VSCODIUM_APP" -> platform_path("$ISABELLE_VSCODIUM_RESOURCES/vscodium"),
        "ELECTRON_RUN_AS_NODE" -> "1"))

    val electron = Isabelle_System.getenv("ISABELLE_VSCODIUM_ELECTRON")
    if (electron.isEmpty) {
      error("""Undefined $ISABELLE_VSCODIUM_ELECTRON: missing "vscodium" component""")
    }
    val args0 =
      List(platform_path("$ISABELLE_VSCODIUM_RESOURCES/vscodium/out/cli.js"), "--locale", "en-US",
        "--user-data-dir", platform_path("$ISABELLE_VSCODE_SETTINGS/user-data"),
        "--extensions-dir", platform_path("$ISABELLE_VSCODE_SETTINGS/extensions"))
    val script =
      Bash.strings(electron :: args0 ::: args) +
        (if (background) " > /dev/null 2> /dev/null &" else "")

    progress.bash(Bash.strings(List(electron, "-v"))).check

    progress.bash(script, env = env, echo = true)
  }


  /* extension */

  def default_vsix_path: Path = Path.explode("$ISABELLE_VSCODE_VSIX")

  def extension_dir: Path = Path.explode("$ISABELLE_VSCODE_HOME/extension")
  val extension_name: String = "isabelle.isabelle"

  val MANIFEST: Path = Path.explode("MANIFEST")

  private def shasum_vsix(vsix_path: Path): SHA1.Shasum = {
    val name = "extension/MANIFEST.shasum"
    def err(): Nothing = error("Cannot retrieve " + quote(name) + " from " + vsix_path)
    if (vsix_path.is_file) {
      using(new ZipFile(vsix_path.file))(zip_file =>
        zip_file.getEntry(name) match {
          case null => err()
          case entry =>
            zip_file.getInputStream(entry) match {
              case null => err()
              case stream => SHA1.fake_shasum(File.read_stream(stream))
            }
        })
    }
    else err()
  }

  private def shasum_dir(dir: Path): Option[SHA1.Shasum] = {
    val path = dir + MANIFEST.shasum
    if (path.is_file) Some(SHA1.fake_shasum(File.read(path))) else None
  }

  def locate_extension(): Option[Path] = {
    val out = run_vscodium(List("--locate-extension", extension_name)).check.out
    if (out.nonEmpty) Some(Path.explode(File.standard_path(out))) else None
  }

  def uninstall_extension(progress: Progress = new Progress): Unit =
    locate_extension() match {
      case None => progress.echo_warning("No Isabelle/VSCode extension to uninstall")
      case Some(dir) =>
        run_vscodium(List("--uninstall-extension", extension_name)).check
        progress.echo("Uninstalled Isabelle/VSCode extension from directory:\n" + dir)
    }

  def install_extension(
    vsix_path: Path = default_vsix_path,
    progress: Progress = new Progress
  ): Unit = {
    val new_shasum = shasum_vsix(vsix_path)
    val old_shasum = locate_extension().flatMap(shasum_dir)
    val current = old_shasum.isDefined && old_shasum.get == new_shasum

    if (!current) {
      run_vscodium(List("--install-extension", File.bash_platform_path(vsix_path))).check
      locate_extension() match {
        case None => error("Missing Isabelle/VSCode extension after installation")
        case Some(dir) =>
          progress.echo("Installed Isabelle/VSCode extension " + vsix_path.expand +
            "\ninto directory: " + dir)
      }
    }
  }


  /* settings */

  def settings_path: Path =
    Path.explode("$ISABELLE_VSCODE_SETTINGS/user-data/User/settings.json")

  private val default_settings = """  {
    "editor.fontFamily": "'Isabelle DejaVu Sans Mono'",
    "editor.fontSize": 18,
    "editor.lineNumbers": "off",
    "editor.renderIndentGuides": false,
    "editor.renderWhitespace": "none",
    "editor.rulers": [80, 100],
    "editor.quickSuggestions": { "strings": "on" },
    "editor.unicodeHighlight.ambiguousCharacters": false,
    "editor.wordBasedSuggestions": false,
    "extensions.autoCheckUpdates": false,
    "extensions.autoUpdate": false,
    "terminal.integrated.fontFamily": "monospace",
    "update.mode": "none"
  }
"""

  def init_settings(): Unit = {
    if (!settings_path.is_file) {
      Isabelle_System.make_directory(settings_path.dir)
      File.write(settings_path, default_settings)
    }
  }


  /* Isabelle tool wrappers */

  val isabelle_tool1 =
    Isabelle_Tool("vscode", "Isabelle/VSCode interface wrapper", Scala_Project.here,
      { args =>
        var logic_ancestor = ""
        var console = false
        val java_options = new StringBuilder(default_java_options)
        var edit_extension = false
        var server_log = false
        var logic_requirements = false
        var uninstall = false
        var vsix_path = default_vsix_path
        val session_dirs = new mutable.ListBuffer[Path]
        val include_sessions = new mutable.ListBuffer[String]
        var logic = Isabelle_System.default_logic()
        val modes = new mutable.ListBuffer[String]
        var no_build = false
        val options = new mutable.ListBuffer[String]
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle vscode [OPTIONS] [ARGUMENTS] [-- VSCODE_OPTIONS]

    -A NAME      ancestor session for option -R (default: parent)
    -C           run as foreground process, with console output
    -D NAME=X    set JVM system property for "isabelle vscode_server"
    -J OPTION    add JVM runtime option for "isabelle vscode_server"
                 (default: $VSCODE_JAVA_OPTIONS=""" + quote(default_java_options) + """)
    -E           edit Isabelle/VSCode extension project sources
    -L           enable language server log to file:
                 """ + server_log_path.implode + """
    -R NAME      build image with requirements from other sessions
    -U           uninstall Isabelle/VSCode extension
    -V FILE      specify VSIX file for Isabelle/VSCode extension
                 (default: """ + default_vsix_path + """)
    -d DIR       include session directory
    -i NAME      include session in name-space of theories
    -l NAME      logic session name
    -m MODE      add print mode for output
    -n           no build of session image on startup
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p CMD       command prefix for ML process (e.g. NUMA policy)
    -s           system build mode for session image (system_heaps=true)
    -u           user build mode for session image (system_heaps=false)
    -v           verbose logging of language server

  Start Isabelle/VSCode application, with automatic configuration of
  user settings.

  The following initial settings are provided for a fresh installation:
""" + default_settings,
          "A:" -> (arg => logic_ancestor = arg),
          "C" -> (_ => console = true),
          "D:" -> { arg => java_options ++= " -D"; java_options ++= arg },
          "E" -> (_ => edit_extension = true),
          "J:" -> { arg => java_options += ' '; java_options ++= arg },
          "L" -> (_ => server_log = true),
          "R:" -> (arg => { logic = arg; logic_requirements = true }),
          "U" -> (_ => uninstall = true),
          "V:" -> (arg => vsix_path = Path.explode(arg)),
          "d:" -> (arg => session_dirs += Path.explode(arg)),
          "i:" -> (arg => include_sessions += arg),
          "l:" -> (arg => { logic = arg; logic_requirements = false }),
          "m:" -> (arg => modes += arg),
          "n" -> (_ => no_build = true),
          "o:" -> (arg => options += arg),
          "p:" -> (arg => options += ("process_policy=" + arg)),
          "s" -> (_ => options += "system_heaps=true"),
          "u" -> (_ => options += "system_heaps=false"),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)

        init_settings()

        val console_progress = new Console_Progress(verbose = true)

        console_progress.interrupt_handler {
          Language_Server.build_session(options.foldLeft(Options.init())(_ + _), logic,
            build_progress = console_progress,
            session_dirs = session_dirs.toList,
            include_sessions = include_sessions.toList,
            session_ancestor = proper_string(logic_ancestor),
            session_requirements = logic_requirements,
            session_no_build = no_build,
            start_message = console_progress.echo(_))
        }

        if (uninstall) uninstall_extension(progress = console_progress)
        else install_extension(vsix_path = vsix_path, progress = console_progress)

        val (background, app_progress) =
          if (console) (false, console_progress) else (true, new Progress)

        run_vscodium(
          more_args ::: (if (edit_extension) List(File.platform_path(extension_dir)) else Nil),
          options = options.toList, java_options = java_options.toString, logic = logic,
          logic_ancestor = logic_ancestor, logic_requirements = logic_requirements,
          session_dirs = session_dirs.toList, include_sessions = include_sessions.toList,
          modes = modes.toList, no_build = no_build, server_log = server_log, verbose = verbose,
          background = background, progress = app_progress).check
      })


  /* Isabelle tool wrapper */

  val isabelle_tool2 =
    Isabelle_Tool("vscode_server", "VSCode Language Server for PIDE", Scala_Project.here,
      { args =>
        try {
          var logic_ancestor: Option[String] = None
          var log_file: Option[Path] = None
          var logic_requirements = false
          val dirs = new mutable.ListBuffer[Path]
          val include_sessions = new mutable.ListBuffer[String]
          var logic = Isabelle_System.default_logic()
          var modes: List[String] = Nil
          var no_build = false
          var options = Options.init()
          var verbose = false

          val getopts = Getopts("""
Usage: isabelle vscode_server [OPTIONS]

  Options are:
    -A NAME      ancestor session for option -R (default: parent)
    -L FILE      logging on FILE
    -R NAME      build image with requirements from other sessions
    -d DIR       include session directory
    -i NAME      include session in name-space of theories
    -l NAME      logic session name (default ISABELLE_LOGIC=""" +
            quote(Isabelle_System.default_logic()) + """)
    -m MODE      add print mode for output
    -n           no build of session image on startup
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose logging

  Run the VSCode Language Server protocol (JSON RPC) over stdin/stdout.
""",
            "A:" -> (arg => logic_ancestor = Some(arg)),
            "L:" -> (arg => log_file = Some(Path.explode(File.standard_path(arg)))),
            "R:" -> (arg => { logic = arg; logic_requirements = true }),
            "d:" -> (arg => dirs += Path.explode(File.standard_path(arg))),
            "i:" -> (arg => include_sessions += arg),
            "l:" -> (arg => logic = arg),
            "m:" -> (arg => modes = arg :: modes),
            "n" -> (_ => no_build = true),
            "o:" -> (arg => options = options + arg),
            "v" -> (_ => verbose = true))

          val more_args = getopts(args)
          if (more_args.nonEmpty) getopts.usage()

          val log = Logger.make_file(log_file)
          val channel = new Channel(System.in, System.out, log, verbose)
          val server =
            new Language_Server(channel, options, session_name = logic, session_dirs = dirs.toList,
              include_sessions = include_sessions.toList, session_ancestor = logic_ancestor,
              session_requirements = logic_requirements, session_no_build = no_build,
              modes = modes, log = log)

          // prevent spurious garbage on the main protocol channel
          val orig_out = System.out
          try {
            System.setOut(new PrintStream(OutputStream.nullOutputStream()))
            server.start()
          }
          finally { System.setOut(orig_out) }
        }
        catch {
          case exn: Throwable =>
            val channel = new Channel(System.in, System.out, new Logger)
            channel.error_message(Exn.message(exn))
            throw(exn)
        }
      })
}
