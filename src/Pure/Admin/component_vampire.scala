/*  Title:      Pure/Admin/component_vampire.scala
    Author:     Makarius

Build Isabelle component for Vampire. See also https://github.com/vprover/vampire
*/

package isabelle


object Component_Vampire {
  /* platform information */

  sealed case class Download_Platform(platform_name: String, download_name: String) {
    def is_windows: Boolean = platform_name.endsWith("-cygwin")
  }

  val platforms: List[Download_Platform] =
    List(
      Download_Platform("arm64-darwin", "vampire-macOS-ARM64.zip"),
      Download_Platform("arm64-linux", "vampire-Linux-ARM64.zip"),
      Download_Platform("x86_64-darwin", "vampire-macOS-X64.zip"),
      Download_Platform("x86_64-linux", "vampire-Linux-X64.zip"),
      Download_Platform("x86_64-cygwin", "vampire-Windows-X64.zip"))


  /* build Vampire */

  val default_url = "https://github.com/vprover/vampire/releases/download"
  val default_version = "5.1.0"

  def build_vampire(
    base_url: String = default_url,
    version: String = default_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    /* component name */

    val component = "vampire-" + version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component)).create(progress = progress)


    /* download executables */

    val download_url = base_url + "/v" + version

    for (platform <- platforms) {
      Isabelle_System.with_tmp_dir("download") { download_dir =>
        val download = download_url + "/" + platform.download_name

        val archive_name =
          Url.get_base_name(platform.download_name) getOrElse
            error("Malformed download name " + quote(platform.download_name))
        val archive_path = download_dir + Path.basic(archive_name)

        val platform_dir = component_dir.path + Path.explode(platform.platform_name)
        Isabelle_System.make_directory(platform_dir)

        val exe_path = Path.explode("vampire").exe_if(platform.is_windows)

        Isabelle_System.download_file(download, archive_path, progress = progress)
        Isabelle_System.extract(archive_path, download_dir)

        Isabelle_System.copy_file(download_dir + exe_path, platform_dir + exe_path)
        File.set_executable(platform_dir + exe_path)
      }
    }


    /* settings */

    component_dir.write_settings("""
VAMPIRE_HOME="$COMPONENT/${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}"
VAMPIRE_VERSION=""" + quote(version) + """

ISABELLE_VAMPIRE="$VAMPIRE_HOME/vampire"
""")


    /* README */

    File.write(component_dir.README,
      "This Isabelle component provides Vampire " + version + """ using the executables
from """ + download_url + """

For Linux, the platform base-line is Ubuntu 22.04 LTS (instead of 22.04).


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_vampire", "build prover component from official download",
    Scala_Project.here,
    { args =>
      var target_dir = Path.current
      var base_url = default_url
      var version = default_version
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle component_vampire [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL
                 (default: """" + default_url + """")
    -V VERSION   version (default: """ + default_version + """)
    -v           verbose

  Build prover component from official download.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "U:" -> (arg => base_url = arg),
        "V:" -> (arg => version = arg),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress(verbose = verbose)

      build_vampire(base_url = base_url, version = version, target_dir = target_dir,
        progress = progress)
    })
}
