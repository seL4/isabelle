/*  Title:      Pure/Admin/component_windows_app.scala
    Author:     Makarius

Auxiliary parts for Isabelle as Windows application.
*/

package isabelle


object Component_Windows_App {
  /* resources */

  def tool_platform(): String = {
    require(Platform.is_unix, "Linux or macOS platform required")
    Isabelle_Platform.local.ISABELLE_PLATFORM64
  }

  val base_path: Path = Path.basic("windows_app")

  def isabelle_exe(base: Path = base_path): Path =
    base + Path.basic("Isabelle.exe")

  def seven_zip_exe(base: Path = base_path): Path =
    base + Path.basic(tool_platform()) + Path.basic("7zz")

  val sfx_name = "7z.sfx"
  def sfx_path(base: Path = base_path): Path = base + Path.basic(sfx_name)


  /* 7zip platform downloads */

  sealed case class Seven_Zip_Platform(name: String, url_template: String) {
    def path: Path = Path.basic(name)
  }

  private val seven_zip_platforms: List[Seven_Zip_Platform] =
    List(
      Seven_Zip_Platform("arm64-linux", "{U}/{V}/7z{v}-linux-arm64.tar.xz"),
      Seven_Zip_Platform("x86_64-darwin", "{U}/{V}/7z{v}-mac.tar.xz"),
      Seven_Zip_Platform("x86_64-linux", "{U}/{V}/7z{v}-linux-x64.tar.xz"))

  private val seven_zip_windows_url_template = "{U}/{V}/7z{v}-x64.exe"
  private val seven_zip_windows = "{U}/{V}/7zr.exe"


  /* build windows_app */

  val default_seven_zip_url = "https://github.com/ip7z/7zip/releases/download"
  val default_seven_zip_version = "26.04"

  def build_windows_app(
    seven_zip_url: String = default_seven_zip_url,
    seven_zip_version: String = default_seven_zip_version,
    progress: Progress = new Progress,
    target_dir: Path = Path.current
  ): Unit = {
    require(Platform.is_windows, "Windows platform required")
    Isabelle_System.require_command("mt.exe", test = "/?")

    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      val component_dir = Components.Directory(tmp_dir + Path.basic("windows_app")).create()


      /* exe manifest */

      def change_manifest(name: String, f: String => String): Unit = {
        Isabelle_System.bash(
          "mt.exe " + Bash.string("-inputresource:" + name + ";#1") + " -out:manifest",
          cwd = tmp_dir).check

        File.change(tmp_dir + Path.basic("manifest"), strict = true)(f)

        Isabelle_System.bash(
          "mt.exe -manifest manifest " + Bash.string("-outputresource:" + name + ";#1"),
          cwd = tmp_dir).check
      }


      /* 7zip tool */

      def make_url(url_template: String): String =
        url_template.replacing(
          "{U}" -> seven_zip_url,
          "{V}" -> seven_zip_version,
          "{v}" -> seven_zip_version.replacing("." -> ""))

      for (platform <- seven_zip_platforms) {
        val url = make_url(platform.url_template)
        val name = Url.get_base_name(url).getOrElse(error("No base name in " + quote(url)))
        val download = tmp_dir + Path.basic(name)
        Isabelle_System.download_file(url, download, progress = progress)
        Isabelle_System.extract(download,
          Isabelle_System.make_directory(tmp_dir + platform.path))
        Isabelle_System.copy_file(tmp_dir + platform.path + Path.basic("7zz"),
          Isabelle_System.make_directory(component_dir.path + platform.path))
      }


      /* 7zip sfx module */

      val windows_url = make_url(seven_zip_windows_url_template)
      val windows_archive = Path.basic(Url.get_base_name(windows_url).get)
      val tmp_7z_exe = tmp_dir + Path.basic("7z.exe")

      Isabelle_System.download_file(windows_url, tmp_dir + windows_archive, progress = progress)
      Isabelle_System.download_file(make_url(seven_zip_windows), tmp_7z_exe, progress = progress)
      File.set_executable(tmp_7z_exe)

      Isabelle_System.bash(
        "./7z x -y " + File.bash_path(windows_archive) + " " + Bash.string(sfx_name),
        cwd = tmp_dir).check

      change_manifest(sfx_name, _.replacing(
        "</dependency>\r\n" ->
        ("</dependency>\r\n" +
          """<trustInfo xmlns="urn:schemas-microsoft-com:asm.v2"><security><requestedPrivileges><requestedExecutionLevel level="asInvoker" uiAccess="false"></requestedExecutionLevel></requestedPrivileges></security></trustInfo>""")
        )
      )

      Isabelle_System.copy_file(sfx_path(base = tmp_dir), component_dir.path)


      /* Java launcher */

      val launcher_dir = Isabelle_System.make_directory(tmp_dir + Path.basic("launcher"))

      val isabelle_setup_jar = Path.explode("isabelle_setup.jar")
      val lib_isabelle_setup_jar = Path.explode("lib") + isabelle_setup_jar

      val isabelle_setup_dir =
        Components.directories().filter(dir => (dir + lib_isabelle_setup_jar).is_file) match {
          case List(dir) => dir
          case Nil => error("No component with " + lib_isabelle_setup_jar)
          case bad =>
            error("Multiple components with " + lib_isabelle_setup_jar + bad.mkString(":\n", "\n", ""))
        }

      Isabelle_System.copy_file(isabelle_setup_dir + lib_isabelle_setup_jar, launcher_dir)
      Isabelle_System.copy_file(Path.explode("~~/lib/logo/isabelle_transparent.ico"), launcher_dir)
      Isabelle_System.bash(
        Library.make_lines(
          "set -e",
          "isabelle_java jpackage --name Isabelle --type app-image --input . " +
            "--main-jar isabelle_setup.jar " +
            "--main-class isabelle.setup.GUI_Test " +
            "--icon isabelle_transparent.ico",
          "chmod 755 Isabelle/Isabelle.exe"),
        cwd = launcher_dir).check
      Isabelle_System.copy_file(
        isabelle_exe(base = launcher_dir + Path.explode("Isabelle")),
        isabelle_exe(base = component_dir.path))


      /* README */

      File.write(component_dir.README,
        """Auxiliary parts for Isabelle as Windows application
===================================================

* 7zip: https://www.7-zip.org

* 7z.sfx: changed manifest for non-admin

* Isabelle.exe: via jpackage


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
    Isabelle_Tool("component_windows_app", "build windows_app component",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var seven_zip_url = default_seven_zip_url
        var seven_zip_version = default_seven_zip_version
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_windows_app [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL for 7zip tool, default:
                 """ + default_seven_zip_url + """
    -V VERSION   version for 7zip download (default: """ + default_seven_zip_version + """)
    -v           verbose

  Build auxiliary parts for Isabelle as Windows application.

  Windows prerequisites:
    - mt.exe from https://learn.microsoft.com/en-us/windows/apps/windows-sdk/downloads
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => seven_zip_url = arg),
          "V:" -> (arg => seven_zip_version = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        build_windows_app(seven_zip_url = seven_zip_url, seven_zip_version = seven_zip_version,
          progress = progress, target_dir = target_dir)
      })
}
