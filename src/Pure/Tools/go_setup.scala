/*  Title:      Pure/Tools/go_setup.scala
    Author:     Makarius

Dynamic setup of Go component.
*/

package isabelle


object Go_Setup {
  /* platform information */

  sealed case class Platform_Info(platform: String, go_platform: String)
  extends Platform.Info {
    def paths: List[String] = List(platform, "pkg/tool/" + go_platform)

    def download(base_url: String, version: String): String = {
      val ext = if (is_windows) ".zip" else ".tar.gz"
      Url.append_path(base_url, "go" + version + "." + go_platform.replace("_", "-") + ext)
    }
  }

  val all_platforms: List[Platform_Info] =
    List(
      Platform_Info("arm64-darwin", "darwin_arm64"),
      Platform_Info("arm64-linux", "linux_arm64"),
      Platform_Info("x86_64-darwin", "darwin_amd64"),
      Platform_Info("x86_64-linux", "linux_amd64"),
      Platform_Info("x86_64-windows", "windows_amd64"))

  def check_platform_spec(spec: String): String =
    Platform.check_spec(all_platforms, spec)


  /* Go download and setup */

  def default_platform: String =
    Isabelle_Platform.self.ISABELLE_PLATFORM(windows = true, apple = true)
  def default_target_dir: Path = Components.default_components_base
  val default_url = "https://go.dev/dl"
  def default_version: String = Isabelle_System.getenv_strict("ISABELLE_GO_VERSION")

  def go_setup(
    platforms: List[String] = List(default_platform),
    base_url: String = default_url,
    version: String = default_version,
    target_dir: Path = default_target_dir,
    progress: Progress = new Progress,
    force: Boolean = false
  ): Unit = {
    platforms.foreach(check_platform_spec)


    /* component directory */

    val component_dir =
      Components.Directory(target_dir + Path.basic("go-" + version)).create(permissive = true)

    progress.echo("Component directory " + component_dir)

    component_dir.write_settings("""
ISABELLE_GOROOT="$COMPONENT"

if [ -n "$ISABELLE_WINDOWS_PLATFORM64" -a -d "$ISABELLE_GOROOT/$ISABELLE_WINDOWS_PLATFORM64" ]; then
  ISABELLE_GOEXE="$ISABELLE_GOROOT/$ISABELLE_WINDOWS_PLATFORM64"
elif [ -n "$ISABELLE_APPLE_PLATFORM64" -a -d "$ISABELLE_GOROOT/$ISABELLE_APPLE_PLATFORM64" ]; then
  ISABELLE_GOEXE="$ISABELLE_GOROOT/$ISABELLE_APPLE_PLATFORM64"
elif [ -d "$ISABELLE_GOROOT/$ISABELLE_PLATFORM64" ]; then
  ISABELLE_GOEXE="$ISABELLE_GOROOT/$ISABELLE_PLATFORM64"
fi
""")

    File.write(component_dir.platform_props,
      (for ((a, b) <- all_platforms.groupBy(_.family_name).iterator)
        yield a + " = " + b.flatMap(_.paths).mkString(" ")
      ).mkString("", "\n", "\n"))

    for (old <- proper_string(Isabelle_System.getenv("ISABELLE_GOROOT"))) {
      Components.update_components(false, Path.explode(old))
    }

    Components.update_components(true, component_dir.path)


    /* download and setup */

    Isabelle_System.with_tmp_dir("download") { download_dir =>
      for (platform <- all_platforms if platforms.exists(platform.is)) {
        val platform_dir = component_dir.path + platform.path
        if (platform_dir.is_dir && !force) {
          progress.echo_warning("Platform " + platform + " already installed")
        }
        else {
          progress.echo("Platform " + platform + " ...")
          progress.expose_interrupt()

          if (force) {
            for (name <- platform.paths) {
              val dir = component_dir.path + Path.explode(name)
              if (dir.is_dir) Isabelle_System.rm_tree(dir)
            }
          }

          val download = platform.download(base_url, version)

          val archive_name =
            Url.get_base_name(download) getOrElse
              error("Malformed download URL " + quote(download))
          val archive_path = download_dir + Path.basic(archive_name)

          Isabelle_System.download_file(download, archive_path)
          Isabelle_System.extract(archive_path, component_dir.path, strip = true)
          Isabelle_System.move_file(component_dir.bin, platform_dir)
        }
      }
    }

    File.find_files(component_dir.path.file, pred = file => File.is_exe(file.getName)).
      foreach(file => File.set_executable(File.path(file)))


    /* README */

    File.write(component_dir.README,
      """This installation of Go has been produced via "isabelle go_setup".


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("go_setup", "dynamic setup of Go component", Scala_Project.here,
      { args =>
        var target_dir = default_target_dir
        var base_url = default_url
        var version = default_version
        var force = false
        var platforms = List(default_platform)

        val getopts = Getopts("""
Usage: isabelle go_setup [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")
    -V VERSION   version (default: """" + default_version + """")
    -f           force fresh installation of specified platforms
    -p PLATFORMS comma-separated list of platform specifications,
                 as family or formal name (default: """ + quote(default_platform) + """)

  Download the Go development environment and configure it as Isabelle
  component. See also https://go.dev
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => base_url = arg),
          "V:" -> (arg => version = arg),
          "f" -> (_ => force = true),
          "p:" -> (arg => platforms = space_explode(',', arg).map(check_platform_spec)))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        go_setup(platforms = platforms, base_url = base_url, version = version,
          target_dir = target_dir, progress = progress, force = force)
      })
}

class Go_Setup extends Setup_Tool("go_setup", "ISABELLE_GO_SETUP") {
  override val test_file: Path = Path.explode("lib/Tools/go")
}
