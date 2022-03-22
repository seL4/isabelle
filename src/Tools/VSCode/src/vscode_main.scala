/*  Title:      Tools/VSCode/src/vscode_main.scala
    Author:     Makarius

Main application entry point for Isabelle/VSCode.
*/

package isabelle.vscode


import isabelle._


object VSCode_Main
{
  /* vscodium command-line interface */

  private def platform_path(s: String): String = File.platform_path(Path.explode(s))

  def run_cli(args: List[String],
    environment: Iterable[(String, String)] = Nil,
    options: List[String] = Nil,
    logic: String = "",
    logic_ancestor: String = "",
    logic_requirements: Boolean = false,
    session_dirs: List[Path] = Nil,
    include_sessions: List[String] = Nil,
    modes: List[String] = Nil,
    no_build: Boolean = false,
    log_file: Option[Path] = None,
    verbose: Boolean = false,
    background: Boolean = false,
    progress: Progress = new Progress): Process_Result =
  {
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
      JSON.optional("log_file" -> log_file.map(_.absolute.implode)) ++
      JSON.optional("verbose" -> proper_bool(verbose))

    val env = new java.util.HashMap(Isabelle_System.settings())
    for ((a, b) <- environment) env.put(a, b)
    env.put("ISABELLE_VSCODIUM_ARGS", JSON.Format(args_json))
    env.put("ISABELLE_VSCODIUM_APP", platform_path("$ISABELLE_VSCODIUM_RESOURCES/vscodium"))
    env.put("ELECTRON_RUN_AS_NODE", "1")

    val electron = Isabelle_System.getenv("ISABELLE_VSCODIUM_ELECTRON")
    if (electron.isEmpty) {
      error("""Undefined $ISABELLE_VSCODIUM_ELECTRON: missing "vscodium" component""")
    }
    val args0 =
      List(platform_path("$ISABELLE_VSCODIUM_RESOURCES/vscodium/out/cli.js"),
        "--ms-enable-electron-run-as-node", "--locale", "en-US",
        "--user-data-dir", platform_path("$ISABELLE_VSCODE_SETTINGS/user-data"),
        "--extensions-dir", platform_path("$ISABELLE_VSCODE_SETTINGS/extensions"))
    val script =
      Bash.strings(electron :: args0 ::: args) +
        (if (background) " > /dev/null 2> /dev/null &" else "")

    progress.bash(script, env = env, echo = true)
  }


  /* settings */

  def settings_path: Path =
    Path.explode("$ISABELLE_VSCODE_SETTINGS/user-data/User/settings.json")

  private val default_settings = """  {
    "editor.fontFamily": "'Isabelle DejaVu Sans Mono'",
    "editor.fontSize": 18,
    "editor.lineNumbers": "off",
    "editor.renderIndentGuides": false,
    "editor.rulers": [80, 100],
    "editor.unicodeHighlight.ambiguousCharacters": false,
    "extensions.autoCheckUpdates": false,
    "extensions.autoUpdate": false,
    "terminal.integrated.fontFamily": "monospace",
    "update.mode": "none"
  }
"""

  def init_settings(): Unit =
  {
    if (!settings_path.is_file) {
      Isabelle_System.make_directory(settings_path.dir)
      File.write(settings_path, default_settings)
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("vscode", "Isabelle/VSCode interface wrapper", Scala_Project.here, args =>
    {
      var logic_ancestor = ""
      var console = false
      var log_file: Option[Path] = None
      var logic_requirements = false
      var session_dirs = List.empty[Path]
      var include_sessions = List.empty[String]
      var logic = ""
      var modes = List.empty[String]
      var no_build = false
      var options = List.empty[String]
      var verbose = false

      def add_option(opt: String): Unit = options = options ::: List(opt)

      val getopts = Getopts("""
Usage: isabelle vscode [OPTIONS] [-- VSCODE_OPTIONS ...]

    -A NAME      ancestor session for option -R (default: parent)
    -C           run as foreground process, with console output
    -L FILE      logging on FILE
    -R NAME      build image with requirements from other sessions
    -d DIR       include session directory
    -i NAME      include session in name-space of theories
    -l NAME      logic session name
    -m MODE      add print mode for output
    -n           no build of session image on startup
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p CMD       ML process command prefix (process policy)
    -s           system build mode for session image (system_heaps=true)
    -u           user build mode for session image (system_heaps=false)
    -v           verbose logging of language server

  Start Isabelle/VSCode application, with automatic configuration of
  user settings.

  The following initial settings are provided for a fresh installation:
""" + default_settings,
        "A:" -> (arg => logic_ancestor = arg),
        "C" -> (_ => console = true),
        "L:" -> (arg => log_file = Some(Path.explode(arg))),
        "R:" -> (arg => { logic = arg; logic_requirements = true }),
        "d:" -> (arg => session_dirs = session_dirs ::: List(Path.explode(arg))),
        "i:" -> (arg => include_sessions = include_sessions ::: List(arg)),
        "l:" -> (arg => { logic = arg; logic_requirements = false }),
        "m:" -> (arg => modes = modes ::: List(arg)),
        "n" -> (_ => no_build = true),
        "o:" -> add_option,
        "p:" -> (arg => add_option("ML_process_policy=" + arg)),
        "s" -> (_ => add_option("system_heaps=true")),
        "u" -> (_ => add_option("system_heaps=false")),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)

      init_settings()

      val (background, progress) =
        if (console) (false, new Console_Progress)
        else { run_cli(List("--version")).check; (true, new Progress) }

      run_cli(more_args, options = options, logic = logic, logic_ancestor = logic_ancestor,
        logic_requirements = logic_requirements, session_dirs = session_dirs,
        include_sessions = include_sessions, modes = modes, no_build = no_build,
        log_file = log_file, verbose = verbose, background = background, progress = progress).check
    })
}
