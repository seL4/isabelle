/*  Title:      Pure/Admin/component_cvc5.scala
    Author:     Makarius

Build Isabelle component for cvc5. See also:

  - https://cvc5.github.io/
  - https://github.com/cvc5/cvc5
*/

package isabelle


object Component_CVC5 {
  /* platform information */

  sealed case class Download_Platform(platform_name: String, download_name: String) {
    def is_arm: Boolean = platform_name.startsWith("arm64-")
    def is_windows: Boolean = platform_name.endsWith("-windows")
  }

  val platforms: List[Download_Platform] =
    List(
      Download_Platform("arm64-darwin", "cvc5-macOS-arm64-static.zip"),
      Download_Platform("arm64-linux", "cvc5-Linux-arm64-static.zip"),
      Download_Platform("x86_64-darwin", "cvc5-macOS-x86_64-static.zip"),
      Download_Platform("x86_64-linux", "cvc5-Linux-x86_64-static.zip"),
      Download_Platform("x86_64-windows", "cvc5-Win64-x86_64-static.zip"))


  /* build cvc5 */

  val default_url = "https://github.com/cvc5/cvc5/releases/download"
  val default_version = "1.2.0"

  def build_cvc5(
    base_url: String = default_url,
    version: String = default_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    /* component name */

    val component = "cvc5-" + version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component)).create(progress = progress)


    /* download executables */

    for (platform <- platforms) {
      Isabelle_System.with_tmp_dir("download") { download_dir =>
        val download = base_url + "/cvc5-" + version + "/" + platform.download_name

        val archive_name =
          Url.get_base_name(platform.download_name) getOrElse
            error("Malformed download name " + quote(platform.download_name))
        val archive_path = download_dir + Path.basic(archive_name)

        val platform_dir = component_dir.path + Path.explode(platform.platform_name)
        Isabelle_System.make_directory(platform_dir)

        val exe_path = Path.explode("cvc5").exe_if(platform.is_windows)
        val exe_bin_path = Path.explode("cvc5-bin").exe_if(platform.is_windows)

        val exe = platform_dir + exe_path
        val exe_bin = platform_dir + exe_bin_path

        Isabelle_System.download_file(download, archive_path, progress = progress)
        Isabelle_System.extract(archive_path, download_dir, strip = true)

        Isabelle_System.copy_file(download_dir + Path.basic("bin") + exe_path, exe_bin)
        File.set_executable(exe_bin)

        File.write(exe, """#!/usr/bin/env bash

"$CVC5_HOME/cvc5-bin" "$@"
""")
        File.set_executable(exe)
      }
    }


  /* settings */

    component_dir.write_settings("""
CVC5_HOME="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}}"
CVC5_VERSION=""" + Bash.string(version) + """

CVC5_SOLVER="$CVC5_HOME/cvc5"

if [ -e "$CVC5_HOME" ]
then
  CVC5_INSTALLED="yes"
fi
""")


    /* README */

    File.write(component_dir.README,
      """This distribution of cvc5 was assembled from official downloads from
""" + base_url + """ --- the static.zip variants
for macOS, Linux, and Windows, with ARM64 support on macOS and Linux.

The downloaded files were renamed and made executable.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")


    /* AUTHORS and COPYING */

    // download "latest" versions as reasonable approximation
    def raw_download(name: String): Unit =
      Isabelle_System.download_file("https://raw.githubusercontent.com/cvc5/cvc5/main/" + name,
        component_dir.path + Path.explode(name))

    raw_download("AUTHORS")
    raw_download("COPYING")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_cvc5", "build component for cvc5", Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var base_url = default_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle component_cvc5 [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")
    -V VERSION   version (default: """" + default_version + """")

  Build component for cvc5 solver.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => base_url = arg),
          "V:" -> (arg => version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_cvc5(base_url = base_url, version = version, target_dir = target_dir,
          progress = progress)
      })
}
