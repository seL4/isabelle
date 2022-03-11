/*  Title:      Tools/VSCode/src/vscode_setup.scala
    Author:     Makarius

Provide user configuration for Isabelle/VSCode.
*/

package isabelle.vscode


import isabelle._


object VSCode_Setup
{
  /* vscode setup */

  def vscode_settings_user: Path =
    Path.explode("$ISABELLE_VSCODE_SETTINGS/user-data/User/settings.json")

  private val init_settings = """  {
    "editor.fontFamily": "'Isabelle DejaVu Sans Mono'",
    "editor.fontSize": 18,
    "editor.lineNumbers": "off",
    "editor.renderIndentGuides": false,
    "editor.rulers": [80, 100],
    "editor.unicodeHighlight.ambiguousCharacters": false,
    "extensions.autoCheckUpdates": false,
    "extensions.autoUpdate": false,
    "files.encoding": "utf8isabelle",
    "terminal.integrated.fontFamily": "monospace",
    "update.mode": "none"
  }
"""

  def vscode_setup(): Unit =
  {
    if (Isabelle_System.getenv("ISABELLE_VSCODIUM_HOME").isEmpty) {
      error("""Missing $ISABELLE_VSCODIUM_HOME: proper vscodium-X.YY.Z component required""")
    }

    if (!vscode_settings_user.is_file) {
      Isabelle_System.make_directory(vscode_settings_user.dir)
      File.write(vscode_settings_user, init_settings)
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("vscode_setup", "provide user configuration for Isabelle/VSCode",
      Scala_Project.here, args =>
    {
      val getopts = Getopts("""
Usage: vscode_setup

  Provide user configuration for Isabelle/VSCode.

  The following initial settings are provided for a fresh installation:
""" + init_settings)

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      vscode_setup()
    })
}
