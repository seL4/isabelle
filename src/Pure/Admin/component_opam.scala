/*  Title:      Pure/Admin/component_opam.scala
    Author:     Makarius

Build Isabelle component for OPAM.
*/

package isabelle


object Component_OPAM {
  /* platform information */

  sealed case class Download_Platform(
    platform_name: String, download_name: String, exe: String = "opam")

  val platforms: List[Download_Platform] =
    List(
      Download_Platform("arm64-darwin", "opam-{V}-arm64-macos"),
      Download_Platform("arm64-linux", "opam-{V}-arm64-linux"),
      Download_Platform("x86_64-darwin", "opam-{V}-x86_64-macos"),
      Download_Platform("x86_64-linux", "opam-{V}-x86_64-linux"),
      Download_Platform("x86_64-windows", "opam-{V}-x86_64-windows.exe", exe = "opam.exe"))


  /* build opam */

  val default_url = "https://github.com/ocaml/opam/releases/download"
  val default_version = "2.5.1"

  def build_opam(
    base_url: String = default_url,
    version: String = default_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    /* component name */

    val component = "opam-" + version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component)).create(progress = progress)


    /* download executables */

    val download_url = base_url + "/" + version

    for (platform <- platforms) {
      Isabelle_System.with_tmp_dir("download") { download_dir =>
        val platform_dir = component_dir.path + Path.explode(platform.platform_name)
        Isabelle_System.make_directory(platform_dir)

        val download = download_url + "/" + platform.download_name.replacing("{V}" -> version)
        val exe = platform_dir + Path.explode(platform.exe)
        Isabelle_System.download_file(download, exe, progress = progress)
        File.set_executable(exe)
      }
    }


  /* settings */

    component_dir.write_settings("""
ISABELLE_OPAM="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}}"
""")


    /* README */

    File.write(component_dir.README,
      """This is OPAM """ + version + """ the OCaml Package Manager.

See also """ + download_url + """

The downloaded files were renamed and made executable.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")


    /* AUTHORS and COPYING */

    def raw_download(name: String): Unit =
      Isabelle_System.download_file(
        "https://raw.githubusercontent.com/ocaml/opam/refs/tags/" + version + "/" + name,
        component_dir.path + Path.explode(name))

    raw_download("AUTHORS")
    raw_download("LICENSE")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_opam", "build component for OPAM", Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var base_url = default_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle component_opam [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")
    -V VERSION   version (default: """" + default_version + """")

  Build component for OPAM.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => base_url = arg),
          "V:" -> (arg => version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_opam(base_url = base_url, version = version, target_dir = target_dir,
          progress = progress)
      })
}
