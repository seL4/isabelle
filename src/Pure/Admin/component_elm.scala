/*  Title:      Pure/Admin/component_elm.scala
    Author:     Fabian Huch, TU Muenchen

Build Isabelle Elm component from official downloads. See also: https://elm-lang.org/
*/

package isabelle


object Component_Elm {
  /* platform information */

  sealed case class Download_Platform(platform_name: String, file_name: String) {
    override def toString: String = platform_name

    def archive_name: String = file_name + ".gz"
    def download(base_url: String, version: String): String =
      base_url + "/" + version + "/" + archive_name

    val exe: Path = Path.basic("elm").exe_if(platform_name.endsWith("-windows"))
  }

  val platforms: List[Download_Platform] =
    List(
      Download_Platform("arm64-darwin", "binary-for-mac-64-bit-ARM"),
      Download_Platform("x86_64-darwin", "binary-for-mac-64-bit"),
      Download_Platform("x86_64-linux", "binary-for-linux-64-bit"),
      Download_Platform("x86_64-windows", "binary-for-windows-64-bit"))


  /* build elm */

  val default_url = "https://github.com/elm/compiler/releases/download"
  val default_version = "0.19.1"

  def build_elm(
    base_url: String = default_url,
    version: String = default_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    Isabelle_System.require_command("gunzip")


    /* component */

    val component = "elm-" + version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component)).create(progress = progress)


    /* download */

    for (platform <- platforms) {
      val platform_dir =
        Isabelle_System.make_directory(component_dir.path + Path.basic(platform.platform_name))

      val download = platform.download(base_url, version)

      Isabelle_System.with_tmp_dir("download", component_dir.path.file) { download_dir =>
        Isabelle_System.with_tmp_dir("tmp", component_dir.path.file) { tmp_dir =>
          val archive_file = download_dir + Path.basic(platform.archive_name)

          Isabelle_System.download_file(download, archive_file, progress = progress)
          Isabelle_System.bash("gunzip " + File.bash_path(archive_file))
          Isabelle_System.copy_file(archive_file.drop_ext, platform_dir + platform.exe)
          File.set_executable(platform_dir + platform.exe)
        }
      }
    }

    /* license */

    File.write(
      component_dir.LICENSE,
      Url.read("https://raw.githubusercontent.com/elm/compiler/master/LICENSE"))


    /* settings */

    component_dir.write_settings("""
ISABELLE_ELM_HOME="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}}"
""")


    /* README */

    File.write(component_dir.README,
      """This Isabelle component provides elm """ + version + """.

See also https://elm-lang.org and executables from """ + base_url + """

        Fabian Huch
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_elm", "build elm component", Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var base_url = default_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle component_elm [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")
    -V VERSION   version (default: """" + default_version + """")

  Build elm component.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => base_url = arg),
          "V:" -> (arg => version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_elm(base_url = base_url, version = version, target_dir = target_dir,
          progress = progress)
    })
}