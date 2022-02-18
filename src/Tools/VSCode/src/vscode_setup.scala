/*  Title:      Tools/VSCode/src/vscode_setup.scala
    Author:     Makarius

Setup VSCode from VSCodium distribution.
*/

package isabelle.vscode


import isabelle._


object VSCode_Setup
{
  /* global resources */

  def vscode_home: Path = Path.variable("ISABELLE_VSCODE_HOME")
  def vscode_settings: Path = Path.variable("ISABELLE_VSCODE_SETTINGS")
  def vscode_version: String = Isabelle_System.getenv_strict("ISABELLE_VSCODE_VERSION")

  def vscode_installation(version: String, platform: Platform.Family.Value): (Boolean, Path) =
    {
      val platform_name =
        if (platform == Platform.Family.windows) Platform.Family.native(platform)
        else Platform.Family.standard(platform)
      val install_dir =
        vscode_settings + Path.basic("installation") +
          Path.basic(version) + Path.basic(platform_name)
      val install_ok = (install_dir + Path.explode("bin/codium")).is_file
      (install_ok, install_dir)
    }


  /* vscode setup */

  val default_download_url: String = "https://github.com/VSCodium/vscodium/releases/download"
  def default_platform: Platform.Family.Value = Platform.family

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
    verbose: Boolean = false,
    progress: Progress = new Progress): Unit =
  {
    val (install_ok, install_dir) = vscode_installation(version, platform)

    if (check) {
      if (install_ok) progress.echo(install_dir.expand.implode)
      else {
        error("Bad Isabelle/VSCode installation: " + install_dir.expand +
          "\n(use \"isabelle vscode_setup\" to download it)")
      }
    }
    else {
      if (install_ok) {
        progress.echo_warning("Isabelle/VSCode installation already present: " + install_dir.expand)
      }

      val name = download_name(version, platform)
      val is_zip = name.endsWith(".zip")
      if (is_zip) Isabelle_System.require_command("unzip", test = "-h")

      Isabelle_System.make_directory(install_dir)
      Isabelle_System.with_tmp_file("download")(download =>
        {
          Isabelle_System.download_file(download_url + "/" + version + "/" + name, download,
            progress = if (verbose) progress else new Progress)
          if (verbose) progress.echo("Installing " + install_dir.expand)
          if (is_zip) {
            Isabelle_System.bash("unzip -x " + File.bash_path(download),
              cwd = install_dir.file).check
          }
          else {
            Isabelle_System.gnutar("-xzf " + File.bash_path(download),
              dir = install_dir).check
          }
          if (platform == Platform.Family.windows) {
            val files1 = File.find_files((install_dir + Path.explode("bin")).file)
            val files2 =
              File.find_files(install_dir.file,
                pred = file => file.getName.endsWith(".exe") || file.getName.endsWith(".dll"))
            for (file <- files1 ::: files2) File.set_executable(File.path(file), true)
          }
        })
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
      var platforms = List(default_platform)
      var verbose = false

      val getopts = Getopts("""
Usage: vscode_setup [OPTIONS]

  Options are:
    -C           check and print installation directory
    -U URL       download URL
                 (default: """" + default_download_url + """")
    -V VERSION   version (default: """" + vscode_version + """")
    -p NAMES     platform families: comma-separated names
                 (""" + commas_quote(Platform.Family.list.map(_.toString)) + """, default: """ +
        quote(default_platform.toString) + """)
    -v           verbose mode

  Maintain local installation of VSCode, see also https://vscodium.com

  Option -C checks the existing installation (without download), and
  prints its directory location.
""",
        "C" -> (_ => check = true),
        "U:" -> (arg => download_url = arg),
        "V:" -> (arg => version = arg),
        "p:" -> (arg => platforms = Library.space_explode(',', arg).map(Platform.Family.parse)),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()
      for (platform <- platforms) {
        vscode_setup(check = check, download_url = download_url, version = version,
          platform = platform, verbose = verbose, progress = progress)
      }
    })
}
