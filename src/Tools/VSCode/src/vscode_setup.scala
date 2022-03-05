/*  Title:      Tools/VSCode/src/vscode_setup.scala
    Author:     Makarius

Setup VSCode from VSCodium distribution.
*/

package isabelle.vscode


import isabelle._

import java.security.MessageDigest
import java.util.Base64


object VSCode_Setup
{
  /* global resources */

  def vscode_home: Path = Path.variable("ISABELLE_VSCODE_HOME")
  def vscode_settings: Path = Path.variable("ISABELLE_VSCODE_SETTINGS")
  def vscode_settings_user: Path = vscode_settings + Path.explode("user-data/User/settings.json")
  def vscode_workspace: Path = Path.variable("ISABELLE_VSCODE_WORKSPACE")
  def version: String = Build_VSCodium.version

  def vscodium_home: Path = Path.variable("ISABELLE_VSCODIUM_HOME")
  def vscodium_home_ok(): Boolean =
    try { vscodium_home.is_dir }
    catch { case ERROR(_) => false }

  def vscode_installation(info: Build_VSCodium.Platform_Info): (Boolean, Path) =
  {
    val install_dir =
      info.platform_dir(vscode_settings + Path.basic("installation") + Path.basic(version))
    val install_ok = Build_VSCodium.vscodium_exe(install_dir).is_file
    (install_ok, install_dir)
  }


  /* patch resources */

  // see https://github.com/microsoft/vscode/blob/main/build/gulpfile.vscode.js
  // function computeChecksum(filename)

  def file_checksum(path: Path): String =
  {
    val digest = MessageDigest.getInstance("MD5")
    digest.update(Bytes.read(path).array)
    Bytes(Base64.getEncoder.encode(digest.digest()))
      .text.replaceAll("=", "")
  }

  def patch_resources(dir: Path): Unit =
  {
    HTML.init_fonts(dir + Path.explode("app/out/vs/base/browser/ui"))

    val workbench_css = dir + Path.explode("app/out/vs/workbench/workbench.desktop.main.css")
    val checksum1 = file_checksum(workbench_css)
    File.append(workbench_css, "\n\n" + HTML.fonts_css_dir(prefix = "../base/browser/ui"))
    val checksum2 = file_checksum(workbench_css)

    val file_name = workbench_css.file_name
    File.change_lines(dir + Path.explode("app/product.json")) { _.map(line =>
      if (line.containsSlice(file_name) && line.contains(checksum1)) {
        line.replace(checksum1, checksum2)
      }
      else line)
    }
  }


  /* workspace */

  def init_workspace(dir: Path): Unit =
  {
    Isabelle_System.make_directory(dir)
    Isabelle_System.chmod("700", dir)

    File.change(dir + Path.explode("symbols.json"), init = true) { _ =>
      JSON.Format(
        for (entry <- Symbol.symbols.entries; code <- entry.code)
          yield JSON.Object(
            "symbol" -> entry.symbol,
            "name" -> entry.name,
            "code" -> code,
            "abbrevs" -> entry.abbrevs
          )
      )
    }
  }


  /* vscode setup */

  def default_platform: Platform.Family.Value = Platform.family

  private val init_settings = """  {
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

  def vscode_setup(
    check: Boolean = false,
    platform: Platform.Family.Value = default_platform,
    quiet: Boolean = false,
    fresh: Boolean = false,
    progress: Progress = new Progress): Unit =
  {
    val platform_info = Build_VSCodium.the_platform_info(platform)
    val (install_ok, install_dir) = vscode_installation(platform_info)

    if (!vscode_settings_user.is_file) {
      Isabelle_System.make_directory(vscode_settings_user.dir)
      File.write(vscode_settings_user, init_settings)
    }

    if (check) {
      if (vscodium_home_ok()) {
        init_workspace(vscode_workspace)
        progress.echo(vscodium_home.expand.implode)
      }
      else if (install_ok) {
        init_workspace(vscode_workspace)
        progress.echo(install_dir.expand.implode)
      }
      else {
        error("Bad Isabelle/VSCode installation: " + install_dir.expand +
          "\n(use \"isabelle vscode_setup\" for download and installation)")
      }
    }
    else {
      if (install_ok) {
        progress.echo_warning("Isabelle/VSCode installation already present: " + install_dir.expand)
      }
      if (!install_ok || fresh) {
        Isabelle_System.make_directory(install_dir)
        platform_info.download(install_dir, progress = if (quiet) new Progress else progress)
        platform_info.patch_resources(install_dir)
        platform_info.setup_executables(install_dir)
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("vscode_setup", "setup VSCode from VSCodium distribution",
      Scala_Project.here, args =>
    {
      var check = false
      var fresh = false
      var platforms = List(default_platform)
      var quiet = false

      val getopts = Getopts("""
Usage: vscode_setup [OPTIONS]

  Options are:
    -C           check and print installation directory
    -f           force fresh installation
    -p NAMES     platform families: comma-separated names
                 (""" + commas_quote(Platform.Family.list.map(_.toString)) + """, default: """ +
        quote(default_platform.toString) + """)
    -q           quiet mode

  Maintain local installation of VSCode, see also https://vscodium.com

  Option -C checks the existing installation (without download), and
  prints its directory location.

  The following initial settings are provided for a fresh installation:
""" + init_settings,
        "C" -> (_ => check = true),
        "f" -> (_ => fresh = true),
        "p:" -> (arg => platforms = Library.space_explode(',', arg).map(Platform.Family.parse)),
        "q" -> (_ => quiet = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()
      for (platform <- platforms) {
        vscode_setup(check = check, platform = platform, quiet = quiet, fresh = fresh, progress = progress)
      }
    })
}
