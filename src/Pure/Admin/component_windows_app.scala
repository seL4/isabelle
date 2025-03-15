/*  Title:      Pure/Admin/component_windows_app.scala
    Author:     Makarius

Build Isabelle windows_app component from GNU binutils and launch4j.
*/

package isabelle


object Component_Windows_App {
  /* resources */

  def tool_platform(): String = {
    require(Platform.is_unix, "Linux or macOS platform required")
    Isabelle_Platform.self.ISABELLE_PLATFORM64
  }

  def tool_platform_path(): Path = Path.basic(tool_platform())

  val base_path: Path = Path.basic("windows_app")

  def launch4j_jar(base: Path = base_path): Path =
    base + tool_platform_path() + Path.basic("launch4j.jar")

  def seven_zip(base: Path = base_path, exe: Boolean = false): Path =
    base + tool_platform_path() + Path.basic("7zip") +
      (if (exe) Path.basic("7zz") else Path.current)

  val sfx_name = "7zsd_All_x64.sfx"
  val sfx_path: Path = base_path + Path.basic(sfx_name)

  val sfx_txt =
""";!@Install@!UTF-8!
GUIFlags="64"
InstallPath="%UserDesktop%"
BeginPrompt="Unpack {ISABELLE_NAME}?"
ExtractPathText="Target directory"
ExtractTitle="Unpacking {ISABELLE_NAME} ..."
Shortcut="Du,{%%T\{ISABELLE_NAME}\{ISABELLE_NAME}.exe},{},{},{},{{ISABELLE_NAME}},{%%T\{ISABELLE_NAME}}"
RunProgram="\"%%T\{ISABELLE_NAME}\{ISABELLE_NAME}.exe\""
AutoInstall="\"%%T\{ISABELLE_NAME}\{ISABELLE_NAME}.exe\" -init"
;!@InstallEnd@!
"""


  /* 7zip platform downloads */

  sealed case class Seven_Zip_Platform(name: String, url_template: String) {
    def url(version: String): String = url_template.replace("{V}", version)
  }

  private val seven_zip_platforms: List[Seven_Zip_Platform] =
    List(
      Seven_Zip_Platform("arm64-linux", "https://www.7-zip.org/a/7z{V}-linux-arm64.tar.xz"),
      Seven_Zip_Platform("x86_64-darwin", "https://www.7-zip.org/a/7z{V}-mac.tar.xz"),
      Seven_Zip_Platform("x86_64-linux", "https://www.7-zip.org/a/7z{V}-linux-x64.tar.xz"))


  /* build windows_app */

  val default_launch4j_url =
    "https://deac-riga.dl.sourceforge.net/project/launch4j/launch4j-3/3.50/launch4j-3.50-linux-x64.tgz"

  val default_binutils_url =
    "https://ftp.gnu.org/gnu/binutils/binutils-2.26.1.tar.gz"

  val default_sfx_url =
    "https://github.com/chrislake/7zsfxmm/releases/download/1.7.1.3901/7zsd_extra_171_3901.7z"

  val default_seven_zip_version = "2409"

  def build_windows_app(
    launch4j_url: String = default_launch4j_url,
    binutils_url: String = default_binutils_url,
    sfx_url: String = default_sfx_url,
    seven_zip_version: String = default_seven_zip_version,
    progress: Progress = new Progress,
    target_dir: Path = Path.current
  ): Unit = {
    val platform_name = tool_platform()

    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      val download_tar = tmp_dir + Path.basic("download.tar.gz")


      /* component */

      val component_dir = Components.Directory(tmp_dir + Path.basic("windows_app")).create()

      val platform_dir =
        Isabelle_System.make_directory(component_dir.path + Path.basic(platform_name))

      val platform_bin_dir = platform_dir + Path.basic("bin")


      /* launch4j */

      Isabelle_System.download_file(launch4j_url, download_tar, progress = progress)
      Isabelle_System.extract(download_tar, platform_dir, strip = true)


      /* GNU binutils */

      Isabelle_System.download_file(binutils_url, download_tar, progress = progress)
      Isabelle_System.extract(download_tar, tmp_dir, strip = true)

      progress.echo("Building GNU binutils for " + platform_name + " ...")
      val build_script =
        List("""./configure --prefix="$PWD/target" --target=x86_64-w64-mingw32""",
          "make", "make install")
      Isabelle_System.bash(build_script.mkString(" && "), cwd = tmp_dir,
        progress_stdout = progress.echo(_, verbose = true),
        progress_stderr = progress.echo(_, verbose = true)).check

      for (name <- List("ld", "windres")) {
        Isabelle_System.copy_file(
          tmp_dir + Path.explode("target/bin") + Path.basic("x86_64-w64-mingw32-" + name),
            platform_bin_dir + Path.basic(name))
      }


      /* 7zip tool */

      seven_zip_platforms.find(platform => platform.name == platform_name) match {
        case Some(platform) =>
          val url = platform.url(seven_zip_version)
          val name = Url.get_base_name(url).getOrElse(error("No base name in " + quote(url)))
          val download = tmp_dir + Path.basic(name)
          Isabelle_System.download_file(url, download, progress = progress)
          Isabelle_System.extract(download,
            Isabelle_System.make_directory(seven_zip(base = component_dir.path)))
        case None => error("No 7zip for platform " + quote(platform_name))
      }


      /* 7zip sfx module */

      val sfx_archive_name = Url.get_base_name(sfx_url).get

      Isabelle_System.download_file(sfx_url,
        tmp_dir + Path.basic(sfx_archive_name), progress = progress)
      Isabelle_System.bash(
        File.bash_path(seven_zip(base = component_dir.path, exe = true)) + " x " +
          Bash.string(sfx_archive_name), cwd = tmp_dir).check
      Isabelle_System.copy_file(tmp_dir + Path.basic(sfx_name), component_dir.path)


      /* README */

      File.write(component_dir.README,
        """Auxiliary parts for Isabelle as Windows application
===================================================

* Application launcher: http://launch4j.sourceforge.net

* Platform binaries "ld" and "windres" from GNU binutils:
  """ + binutils_url + build_script.mkString("\n\n    ", "\n    ", "") + """

* Self-extracting installer:
  """ + sfx_url + """

See also Isabelle/Admin/Windows/.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")


      /* component archive */

      val component_archive =
        Isabelle_System.make_directory(target_dir) +
          Path.basic("windows_app-" + Date.Format.alt_date(Date.now())).tar.gz

      Isabelle_System.gnutar(
        "-czf " + File.bash_path(component_archive) + " windows_app", dir = tmp_dir).check

      progress.echo("Component archive " + component_archive)
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_windows_app",
        "build windows_app component from GNU binutils and launch4j",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var launch4j_url = default_launch4j_url
        var binutils_url = default_binutils_url
        var sfx_url = default_sfx_url
        var seven_zip_version = default_seven_zip_version
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_windows_app [OPTIONS]

  Options are:
    -B           build GNU binutils from sources
    -D DIR       target directory (default ".")
    -U URL       download URL for launch4j, default:
                 """ + default_launch4j_url + """
    -V URL       download URL for GNU binutils, default:
                 """ + default_binutils_url + """
    -W URL       download URL for 7zip sfx module, default:
                 """ + default_sfx_url + """
    -X VERSION   version for 7zip download (default: """ + default_seven_zip_version + """)
    -v           verbose

  Build Isabelle windows_app component from GNU binutils and launch4j.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => launch4j_url = arg),
          "V:" -> (arg => binutils_url = arg),
          "W:" -> (arg => sfx_url = arg),
          "X:" -> (arg => seven_zip_version = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        build_windows_app(launch4j_url = launch4j_url, binutils_url = binutils_url,
          sfx_url = sfx_url, seven_zip_version = seven_zip_version,
          progress = progress, target_dir = target_dir)
      })
}
