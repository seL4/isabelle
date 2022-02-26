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
  def vscode_version: String = Isabelle_System.getenv_strict("ISABELLE_VSCODE_VERSION")

  def exe_path(dir: Path): Path = dir + Path.explode("bin/codium")

  def vscode_installation(version: String, platform: Platform.Family.Value): (Boolean, Path) =
  {
    val platform_name =
      if (platform == Platform.Family.windows) Platform.Family.native(platform)
      else Platform.Family.standard(platform)
    val install_dir =
      vscode_settings + Path.basic("installation") +
        Path.basic(version) + Path.basic(platform_name)
    val install_ok = exe_path(install_dir).is_file
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
    File.change(dir + Path.explode("app/product.json"), text =>
      cat_lines(split_lines(text).map(line =>
        if (line.containsSlice(file_name) && line.contains(checksum1)) {
          line.replace(checksum1, checksum2)
        }
        else line
      )))
  }


  /* vscode setup */

  val default_download_url: String = "https://github.com/VSCodium/vscodium/releases/download"
  def default_platform: Platform.Family.Value = Platform.family

  private def macos_exe: String =
"""#!/usr/bin/env bash

unset CDPATH
VSCODE_PATH="$(cd "$(dirname "$0")"/../VSCodium.app/Contents; pwd)"

ELECTRON="$VSCODE_PATH/MacOS/Electron"
CLI="$VSCODE_PATH/Resources/app/out/cli.js"
ELECTRON_RUN_AS_NODE=1 "$ELECTRON" "$CLI" --ms-enable-electron-run-as-node "$@"
exit $?
"""

  def download_name(version: String, platform: Platform.Family.Value): String =
  {
    val a = "VSCodium"
    val (b, c) =
      platform match {
        case Platform.Family.linux_arm => ("linux-arm64", "tar.gz")
        case Platform.Family.linux => ("linux-x64", "tar.gz")
        case Platform.Family.macos => ("darwin-x64", "zip")
        case Platform.Family.windows => ("win32-x64", "zip")
      }
    a + "-" + b + "-" + version + "." + c
  }

  def vscode_setup(
    check: Boolean = false,
    download_url: String = default_download_url,
    version: String = vscode_version,
    platform: Platform.Family.Value = default_platform,
    quiet: Boolean = false,
    fresh: Boolean = false,
    progress: Progress = new Progress): Unit =
  {
    val (install_ok, install_dir) = vscode_installation(version, platform)

    if (check) {
      if (install_ok) progress.echo(install_dir.expand.implode)
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
        val name = download_name(version, platform)
        val is_zip = name.endsWith(".zip")
        if (is_zip) Isabelle_System.require_command("unzip", test = "-h")

        Isabelle_System.make_directory(install_dir)
        val exe = exe_path(install_dir)

        Isabelle_System.with_tmp_file("download")(download =>
        {
          Isabelle_System.download_file(download_url + "/" + version + "/" + name, download,
            progress = if (quiet) new Progress else progress)
          if (!quiet) progress.echo("Installing " + install_dir.expand)
          if (is_zip) {
            Isabelle_System.bash("unzip -x " + File.bash_path(download),
              cwd = install_dir.file).check
          }
          else {
            Isabelle_System.gnutar("-xzf " + File.bash_path(download),
              dir = install_dir).check
          }

          platform match {
            case Platform.Family.macos =>
              Isabelle_System.make_directory(exe.dir)
              File.write(exe, macos_exe)
              File.set_executable(exe, true)
            case Platform.Family.windows =>
              val files1 = File.find_files(exe.dir.file)
              val files2 =
                File.find_files(install_dir.file,
                  pred = file => file.getName.endsWith(".exe") || file.getName.endsWith(".dll"))
              for (file <- files1 ::: files2) File.set_executable(File.path(file), true)
            case _ =>
          }

          patch_resources(
            if (platform == Platform.Family.macos) {
              install_dir + Path.explode("VSCodium.app/Contents/Resources")
            }
            else install_dir + Path.explode("resources"))
        })
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("vscode_setup", "setup VSCode from VSCodium distribution",
      Scala_Project.here, args =>
    {
      var check = false
      var download_url = default_download_url
      var version = vscode_version
      var fresh = false
      var platforms = List(default_platform)
      var quiet = false

      val getopts = Getopts("""
Usage: vscode_setup [OPTIONS]

  Options are:
    -C           check and print installation directory
    -U URL       download URL
                 (default: """" + default_download_url + """")
    -V VERSION   version (default: """" + vscode_version + """")
    -f           force fresh installation
    -p NAMES     platform families: comma-separated names
                 (""" + commas_quote(Platform.Family.list.map(_.toString)) + """, default: """ +
        quote(default_platform.toString) + """)
    -q           quiet mode

  Maintain local installation of VSCode, see also https://vscodium.com

  Option -C checks the existing installation (without download), and
  prints its directory location.
""",
        "C" -> (_ => check = true),
        "U:" -> (arg => download_url = arg),
        "V:" -> (arg => version = arg),
        "f" -> (_ => fresh = true),
        "p:" -> (arg => platforms = Library.space_explode(',', arg).map(Platform.Family.parse)),
        "q" -> (_ => quiet = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()
      for (platform <- platforms) {
        vscode_setup(check = check, download_url = download_url, version = version,
          platform = platform, quiet = quiet, fresh = fresh, progress = progress)
      }
    })
}
