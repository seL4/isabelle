/*  Title:      Pure/Admin/component_stack.scala
    Author:     Makarius

Build Isabelle component for GHC stack. See also:

  - https://www.haskellstack.org
  - https://github.com/commercialhaskell
*/

package isabelle


object Component_Stack {
  /* platform information */

  sealed case class Download_Platform(platform_name: String, download_name: String) {
    def is_windows: Boolean = platform_name.endsWith("-windows")
  }

  val platforms: List[Download_Platform] =
    List(
      Download_Platform("arm64-darwin", "osx-aarch64"),
      Download_Platform("arm64-linux", "linux-aarch64"),
      Download_Platform("x86_64-darwin", "osx-x86_64"),
      Download_Platform("x86_64-linux", "linux-x86_64"),
      Download_Platform("x86_64-windows", "windows-x86_64"))


  /* build stack */

  val default_url = "https://github.com/commercialhaskell/stack/releases/download"
  val default_version = "2.15.3"

  def build_stack(
    base_url: String = default_url,
    version: String = default_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    /* component name */

    val component = "stack-" + version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component)).create(progress = progress)


    /* download executables */

    for (platform <- platforms) {
      val platform_dir =
        Isabelle_System.make_directory(component_dir.path + Path.explode(platform.platform_name))

      val url =
        Url.append_path(base_url,
          "v" + version + "/stack-" + version + "-" + platform.download_name + ".tar.gz")

      val exe = Path.explode("stack").exe_if(platform.is_windows)

      Isabelle_System.with_tmp_file("archive", ext = "tar.gz") { archive_file =>
        Isabelle_System.with_tmp_dir("tmp") { tmp_dir =>
          Isabelle_System.download_file(url, archive_file, progress = progress)
          Isabelle_System.extract(archive_file, tmp_dir, strip = true)
          Isabelle_System.move_file(tmp_dir + exe, platform_dir)
          File.set_executable(platform_dir + exe)
        }
      }
    }


    /* settings */

    component_dir.write_settings("""
ISABELLE_STACK="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}}/stack"
""")


    /* README */

    File.write(component_dir.README,
      """This is stack """ + version + """ -- the Haskell Tool Stack.

See also https://www.haskellstack.org and executables from
""" + base_url + """

The downloaded files were renamed and made executable.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")


    /* AUTHORS and COPYING */

    // download "latest" versions as reasonable approximation
    Isabelle_System.download_file("https://raw.githubusercontent.com/commercialhaskell/stack/master/LICENSE",
        component_dir.LICENSE)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_stack", "build component for GHC stack", Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var base_url = default_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle component_stack [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")
    -V VERSION   version (default: """" + default_version + """")

  Build component for GHC stack.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => base_url = arg),
          "V:" -> (arg => version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_stack(base_url = base_url, version = version, target_dir = target_dir,
          progress = progress)
      })
}
