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

  def launch4j_jar(): Path =
    Path.explode("windows_app/" + tool_platform() + "/launch4j.jar")

  val sfx_name = "7zsd_All_x64.sfx"
  val sfx_path: Path = Path.basic("windows_app") + Path.basic(sfx_name)


  /* build windows_app */

  val default_launch4j_url =
    "https://deac-riga.dl.sourceforge.net/project/launch4j/launch4j-3/3.50/launch4j-3.50-linux-x64.tgz"

  val default_binutils_url =
    "https://ftp.gnu.org/gnu/binutils/binutils-2.26.1.tar.gz"

  val default_sfx_url =
    "https://github.com/chrislake/7zsfxmm/releases/download/1.7.1.3901/7zsd_extra_171_3901.7z"

  def build_windows_app(
    launch4j_url: String = default_launch4j_url,
    binutils_url: String = default_binutils_url,
    sfx_url: String = default_sfx_url,
    progress: Progress = new Progress,
    target_dir: Path = Path.current
  ): Unit = {
    Isabelle_System.require_command("7z", test = "")

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


      /* 7zip sfx module */

      val sfx_archive_name = Url.get_base_name(sfx_url).get

      Isabelle_System.download_file(sfx_url,
        tmp_dir + Path.basic(sfx_archive_name), progress = progress)
      Isabelle_System.bash("7z x " + Bash.string(sfx_archive_name), cwd = tmp_dir).check
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
    -v           verbose

  Build Isabelle windows_app component from GNU binutils and launch4j.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => launch4j_url = arg),
          "V:" -> (arg => binutils_url = arg),
          "W:" -> (arg => sfx_url = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        build_windows_app(launch4j_url = launch4j_url, binutils_url = binutils_url,
          sfx_url = sfx_url, progress = progress, target_dir = target_dir)
      })
}
