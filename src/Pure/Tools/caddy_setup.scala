/*  Title:      Pure/Tools/caddy_setup.scala
    Author:     Makarius

Dynamic setup of Caddy component.
*/

package isabelle


object Caddy_Setup {
  /* platform information */

  sealed case class Platform_Info(platform: String, xcaddy_template: String)
  extends Platform.Info {
    def xcaddy_download(url: String, version: String): String =
      Url.append_path(url, xcaddy_template.replace("{V}", version))
  }

  val all_platforms: List[Platform_Info] =
    List(
      Platform_Info("arm64-darwin", "v{V}/xcaddy_{V}_mac_arm64.tar.gz"),
      Platform_Info("arm64-linux", "v{V}/xcaddy_{V}_linux_arm64.tar.gz"),
      Platform_Info("x86_64-darwin", "v{V}/xcaddy_{V}_mac_amd64.tar.gz"),
      Platform_Info("x86_64-linux", "v{V}/xcaddy_{V}_linux_amd64.tar.gz"),
      Platform_Info("x86_64-windows", "v{V}/xcaddy_{V}_windows_amd64.zip"))


  /* download and setup */

  def default_target_dir: Path = Components.default_components_base
  def default_caddy_version: String = Isabelle_System.getenv_strict("ISABELLE_CADDY_SETUP_VERSION")
  def default_caddy_modules: String = Isabelle_System.getenv_strict("ISABELLE_CADDY_SETUP_MODULES")
  def default_xcaddy_url: String = "https://github.com/caddyserver/xcaddy/releases/download"
  def default_xcaddy_version: String = "0.4.4"

  def show_settings(): List[String] =
    for (a <- List("ISABELLE_CADDY_SETUP_VERSION", "ISABELLE_CADDY_SETUP_MODULES"))
      yield {
        val b = Isabelle_System.getenv(a)
        a + "=" + quote(b)
      }

  def caddy_setup(
    caddy_version: String = default_caddy_version,
    caddy_modules: String = default_caddy_modules,
    xcaddy_url: String = default_xcaddy_url,
    xcaddy_version: String = default_xcaddy_version,
    target_dir: Path = default_target_dir,
    progress: Progress = new Progress,
    force: Boolean = false
  ): Unit = {
    val platform = Isabelle_Platform.local.ISABELLE_PLATFORM(windows = true, apple = true)


    /* component directory */

    val component_dir =
      Components.Directory(target_dir + Path.basic("caddy-" + caddy_version))
        .create(permissive = true)

    progress.echo("Component directory " + component_dir)

    component_dir.write_settings("""
ISABELLE_CADDY_HOME="$COMPONENT"

if [ -n "$ISABELLE_WINDOWS_PLATFORM64" -a -d "$ISABELLE_CADDY_HOME/$ISABELLE_WINDOWS_PLATFORM64" ]; then
  ISABELLE_CADDY="$ISABELLE_CADDY_HOME/$ISABELLE_WINDOWS_PLATFORM64/caddy.exe"
elif [ -n "$ISABELLE_APPLE_PLATFORM64" -a -d "$ISABELLE_CADDY_HOME/$ISABELLE_APPLE_PLATFORM64" ]; then
  ISABELLE_CADDY="$ISABELLE_CADDY_HOME/$ISABELLE_APPLE_PLATFORM64/caddy"
elif [ -d "$ISABELLE_CADDY_HOME/$ISABELLE_PLATFORM64" ]; then
  ISABELLE_CADDY="$ISABELLE_CADDY_HOME/$ISABELLE_PLATFORM64/caddy"
fi
""")

    for (old <- proper_string(Isabelle_System.getenv("ISABELLE_CADDY_HOME"))) {
      Components.update_components(false, Path.explode(old))
    }

    Components.update_components(true, component_dir.path)


    /* download and setup */

    Isabelle_System.with_tmp_dir("tmp") { tmp_dir =>
      val platform_info: Platform_Info =
        all_platforms.find(_.platform == platform)
          .getOrElse(error("Bad platform " + quote(platform)))

      val platform_dir = component_dir.path + platform_info.path
      if (platform_dir.is_dir && !force) {
        progress.echo_warning("Platform " + platform + " already installed")
      }
      else {
        progress.echo("Platform " + platform + " ...")
        progress.expose_interrupt()

        Isabelle_System.make_directory(platform_dir)

        val xcaddy_dir = Isabelle_System.make_directory(tmp_dir + Path.explode("xcaddy"))
        val xcaddy_download = platform_info.xcaddy_download(xcaddy_url, xcaddy_version)

        val xcaddy_archive_name =
          Url.get_base_name(xcaddy_download) getOrElse
            error("Malformed download URL " + quote(xcaddy_download))
        val xcaddy_archive_path = tmp_dir + Path.basic(xcaddy_archive_name)

        Isabelle_System.download_file(xcaddy_download, xcaddy_archive_path)
        Isabelle_System.extract(xcaddy_archive_path, xcaddy_dir)

        progress.echo("Building caddy " + caddy_version)
        progress.bash(
          Library.make_lines(
            "set -e",
            "xcaddy/xcaddy build v" + Bash.string(caddy_version) +
              Word.explode(caddy_modules).map(s => " --with " + Bash.string(s)).mkString,
            "./caddy list-modules"),
          cwd = tmp_dir, echo = progress.verbose).check

        Isabelle_System.copy_file(tmp_dir + Path.explode("caddy").platform_exe, platform_dir)
      }
    }

    File.find_files(component_dir.path.file, pred = file => File.is_exe(file.getName)).
      foreach(file => File.set_executable(File.path(file)))


    /* README */

    File.write(component_dir.README,
      """This installation of Caddy has been produced via "isabelle caddy_setup".


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("caddy_setup", "dynamic setup of Caddy component", Scala_Project.here,
      { args =>
        var target_dir = default_target_dir
        var xcaddy_url = default_xcaddy_url
        var xcaddy_version = default_xcaddy_version
        var caddy_modules = default_caddy_modules
        var caddy_version = default_caddy_version
        var force = false
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle caddy_setup [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -N MODULES   non-standard modules for caddy
                 (default: ISABELLE_CADDY_SETUP_MODULES="""" + default_caddy_modules + """")
    -U URL       download URL for xcaddy (default: """" + default_xcaddy_url + """")
    -V VERSION   version for caddy
                 (default: ISABELLE_CADDY_SETUP_VERSION="""" + default_caddy_version + """")
    -W VERSION   version for xcaddy (default: """" + default_xcaddy_version + """")
    -f           force fresh installation of specified platforms
    -v           verbose

  Build the Caddy webserver via xcaddy and configure it as Isabelle
  component. See also https://github.com/caddyserver/xcaddy""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "N:" -> (arg => caddy_modules = arg),
          "U:" -> (arg => xcaddy_url = arg),
          "V:" -> (arg => caddy_version = arg),
          "W:" -> (arg => xcaddy_version = arg),
          "f" -> (_ => force = true),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        caddy_setup(caddy_version = caddy_version, caddy_modules = caddy_modules,
          xcaddy_url = xcaddy_url, xcaddy_version = xcaddy_version, target_dir = target_dir,
          progress = progress, force = force)
      })
}

class Caddy_Setup extends Setup_Tool("caddy_setup", "ISABELLE_CADDY_SETUP") {
  override val test_file: Path = Path.explode("lib/Tools/caddy")
}
