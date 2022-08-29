/*  Title:      Pure/Admin/build_cvc5scala
    Author:     Makarius

Build Isabelle component for cvc5. See also:

  - https://cvc5.github.io/
  - https://github.com/cvc5/cvc5
*/

package isabelle


object Build_CVC5 {
  /* platform information */

  sealed case class CVC5_Platform(platform_name: String, download_name: String) {
    def is_windows: Boolean = platform_name.endsWith("-windows")
  }

  val platforms: List[CVC5_Platform] =
    List(
      CVC5_Platform("arm64-darwin", "cvc5-macOS-arm64"),
      CVC5_Platform("x86_64-darwin", "cvc5-macOS"),
      CVC5_Platform("x86_64-linux", "cvc5-Linux"),
      CVC5_Platform("x86_64-windows", "cvc5-Win64.exe"))


  /* build cvc5 */

  val default_url = "https://github.com/cvc5/cvc5/releases/download"
  val default_version = "1.0.2"

  def build_cvc5(
    base_url: String = default_url,
    version: String = default_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    /* component name */

    val component = "cvc5-" + version
    val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component))
    progress.echo("Component " + component_dir)


    /* download executables */

    for (platform <- platforms) {
      val url = base_url + "/cvc5-" + version + "/" + platform.download_name

      val platform_dir = component_dir + Path.explode(platform.platform_name)
      val platform_exe = platform_dir + Path.explode("cvc5").exe_if(platform.is_windows)

      Isabelle_System.make_directory(platform_dir)
      Isabelle_System.download_file(url, platform_exe, progress = progress)
      File.set_executable(platform_exe, true)
    }


    /* settings */

    val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
    File.write(etc_dir + Path.basic("settings"),
      """# -*- shell-script -*- :mode=shellscript:

CVC5_HOME="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}}"
CVC5_VERSION=""" + Bash.string(version) + """

CVC5_SOLVER="$CVC5_HOME/cvc5"

if [ -e "$CVC5_HOME" ]
then
  CVC5_INSTALLED="yes"
fi
""")


    /* README */

    File.write(component_dir + Path.basic("README"),
      """This distribution of cvc5 was assembled from the official downloads
from """ + base_url + """ for 64bit macOS,
Linux, and Windows. There is native support for macOS ARM64, but
Linux ARM64 is missing.

The oldest supported version of macOS is 10.14 Mojave.

The downloaded files were renamed and made executable.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")


    /* AUTHORS and COPYING */

    // download "latest" versions as reasonable approximation
    def raw_download(name: String): Unit =
      Isabelle_System.download_file("https://raw.githubusercontent.com/cvc5/cvc5/main/" + name,
        component_dir + Path.explode(name))

    raw_download("AUTHORS")
    raw_download("COPYING")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_cvc5", "build component for cvc5", Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var base_url = default_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle build_cvc5 [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")
    -V VERSION   version (default: """" + default_version + """")

  Build component for Java Chromium Embedded Framework.
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
