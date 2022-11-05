/*  Title:      Pure/Tools/dotnet_setup.scala
    Author:     Makarius

Dynamic setup of dotnet component.
*/

package isabelle


object Dotnet_Setup {
  /* platforms */

  sealed case class Platform_Info(
    family: Platform.Family.Value,
    name: String,
    os: String = "",
    arch: String = "x64",
    ext: String = "sh",
    exec: String = "bash",
    check: () => Unit = () => ())

  val all_platforms =
    List(
      Platform_Info(Platform.Family.linux_arm, "arm64-linux", os = "linux", arch = "arm64"),
      Platform_Info(Platform.Family.linux, "x86_64-linux", os = "linux"),
      Platform_Info(Platform.Family.macos, "arm64-darwin", os = "osx", arch = "arm64"),
      Platform_Info(Platform.Family.macos, "x86_64-darwin", os = "osx"),
      Platform_Info(Platform.Family.windows, "x86_64-windows",
        ext = "ps1",
        exec = "powershell -ExecutionPolicy ByPass",
        check = () => Isabelle_System.require_command("powershell", "-NoProfile -Command Out-Null")))

  def check_platform_spec(spec: String): String = {
    val all_specs =
      Library.distinct(all_platforms.map(_.family.toString) ::: all_platforms.map(_.name))
    if (all_specs.contains(spec)) spec
    else {
      error("Bad platform specification " + quote(spec) +
        "\n  expected " + commas_quote(all_specs))
    }
  }


  /* dotnet download and setup */

  def default_platform: String = {
    val self = Isabelle_Platform.self
    proper_string(self.ISABELLE_WINDOWS_PLATFORM64).getOrElse(
      proper_string(self.ISABELLE_APPLE_PLATFORM64).getOrElse(
        self.ISABELLE_PLATFORM64))
  }

  def default_target_dir: Path = Path.explode("$ISABELLE_COMPONENTS_BASE")
  def default_install_url: String = "https://dot.net/v1/dotnet-install"
  def default_version: String = "6.0.402"

  private val settings = """# -*- shell-script -*- :mode=shellscript:

if [ -n "$ISABELLE_WINDOWS_PLATFORM64" -a -d "$COMPONENT/$ISABELLE_WINDOWS_PLATFORM64" ]; then
  ISABELLE_DOTNET="$COMPONENT/$ISABELLE_WINDOWS_PLATFORM64/dotnet.exe"
elif [ -n "$ISABELLE_APPLE_PLATFORM64" -a -d "$COMPONENT/$ISABELLE_APPLE_PLATFORM64" ]; then
  ISABELLE_DOTNET="$COMPONENT/$ISABELLE_APPLE_PLATFORM64/dotnet"
elif [ -d "$COMPONENT/$ISABELLE_PLATFORM64" ]; then
  ISABELLE_DOTNET="$COMPONENT/$ISABELLE_PLATFORM64/dotnet"
fi
"""

  def dotnet_setup(
    platform_spec: String = default_platform,
    target_dir: Path = default_target_dir,
    install_url: String = default_install_url,
    version: String = default_version,
    dry_run: Boolean = false,
    verbose: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    check_platform_spec(platform_spec)

    for {
      platform <- all_platforms
      if platform.family.toString == platform_spec || platform.name == platform_spec
    } {
      progress.expose_interrupt()
      platform.check()


      /* component directory */

      val component_dir =
        target_dir + Path.explode(if (version.isEmpty) "dotnet-latest" else "dotnet-" + version)

      if (!dry_run) {
        val etc_dir = Isabelle_System.make_directory(component_dir + Path.explode("etc"))
        val settings_path = etc_dir + Path.explode("settings")
        if (!settings_path.is_file) {
          progress.echo("Component " + component_dir.expand)
          File.write(settings_path, settings)
        }

        File.write(component_dir + Path.explode("README"),
          """This installation of Dotnet has been produced via "isabelle dotnet_setup".


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")

        Components.update_components(true, component_dir)
      }


      /* platform directory */

      Isabelle_System.with_tmp_file("install", ext = platform.ext) { install =>
        Isabelle_System.download_file(install_url + "." + platform.ext, install)

        val platform_dir = component_dir + Path.explode(platform.name)
        if (platform_dir.is_dir) {
          progress.echo_warning("Platform " + platform.name + " already installed")
        }
        else {
          progress.echo("Platform " + platform.name + " ...")
          val script =
            platform.exec + " " + File.bash_platform_path(install) +
              (if (version.nonEmpty) " -Version " + Bash.string(version) else "") +
              " -Architecture " + Bash.string(platform.arch) +
              (if (platform.os.nonEmpty) " -OS " + Bash.string(platform.os) else "") +
              " -InstallDir " + Bash.string(platform.name) +
              (if (dry_run) " -DryRun" else "") +
              " -NoPath"
          progress.bash(script, echo = verbose,
            cwd = if (dry_run) null else component_dir.file).check
        }
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("dotnet_setup", "dynamic setup of dotnet component (for Fsharp)",
      Scala_Project.here,
      { args =>

        var target_dir = default_target_dir
        var install_url = default_install_url
        var version = default_version
        var dry_run = false
        var platforms = List(default_platform)
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle dotnet_setup [OPTIONS]

  Options are:
    -D DIR       target directory (default: """ + default_target_dir.expand + """)
    -I URL       URL for install script without extension (default: """ + quote(default_install_url) + """)
    -V VERSION   version (empty means "latest", default: """ + quote(default_version) + """)
    -n           dry run: try download without installation
    -p PLATFORMS list of platforms as family or formal name, separated by commas
                 (default: """ + quote(default_platform) + """
    -v           verbose

  Download the Dotnet / Fsharp platform and configure it as Isabelle component.

  See also:
    https://fsharp.org
    https://learn.microsoft.com/en-us/dotnet/core/tools/dotnet-install-script
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "I:" -> (arg => install_url = arg),
          "V:" -> (arg => version = arg),
          "n" -> (_ => dry_run = true),
          "p:" -> (arg => platforms = Library.space_explode(',', arg).map(check_platform_spec)),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        for (platform <- platforms) {
          dotnet_setup(platform_spec = platform, target_dir = target_dir, install_url = install_url,
            version = version, dry_run = dry_run, verbose = verbose, progress = progress)
        }
      })
}
