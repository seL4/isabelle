/*  Title:      Tools/VSCode/src/vscode_main.scala
    Author:     Makarius

Main application entry point for Isabelle/VSCode.
*/

package isabelle.vscode


import isabelle._


object VSCode_Main
{
  /* command-line interface */

  private def platform_path(s: String): String = File.platform_path(Path.explode(s))

  def run_cli(args: List[String],
    environment: Iterable[(String, String)] = Nil,
    background: Boolean = false,
    progress: Progress = new Progress): Process_Result =
  {
    val env = new java.util.HashMap(Isabelle_System.settings())
    for ((a, b) <- environment) env.put(a, b)
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

    Isabelle_System.bash(script, env = env)
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
      val getopts = Getopts("""
Usage: isabelle vscode -- VSCODE_OPTIONS

  Start Isabelle/VSCode application, with automatic configuration of
  user settings.

  The following initial settings are provided for a fresh installation:
""" + default_settings)

      val more_args = getopts(args)

      val progress = new Console_Progress()

      init_settings()
      run_cli(List("--version")).check
      run_cli(more_args, background = true, progress = progress).check
    })
}
