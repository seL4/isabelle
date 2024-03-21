/*  Title:      Pure/Admin/component_mlton.scala
    Author:     Makarius

Build Isabelle component for MLton. See also:

  - http://mlton.org
  - https://projects.laas.fr/tina/software.php
*/

package isabelle


object Component_MLton {
  /* platform information */

  sealed case class Download_Platform(platform_name: String, download_name: String) {
    def download(base_url: String, version: String): String =
      Url.append_path(base_url, version + "." + download_name)
  }

  val platforms: List[Download_Platform] =
    List(
      Download_Platform("arm64-darwin", "arm64-darwin-21.6-gmp-static.tgz"),
      Download_Platform("x86_64-darwin", "amd64-darwin-16.7-gmp-static.tgz"),
      Download_Platform("x86_64-linux", "amd64-linux-glibc2.19-gmp-static.tgz"))


  /* build mlton */

  val default_url = "https://projects.laas.fr/tina/software"
  val default_version = "mlton-20210117-1"

  def build_mlton(
    base_url: String = default_url,
    version: String = default_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    val component_dir =
      Components.Directory(target_dir + Path.basic(version)).create(progress = progress)


    /* download executables */

    for (platform <- platforms) {
      Isabelle_System.with_tmp_dir("download") { download_dir =>
        val download = platform.download(base_url, version)

        val archive_name =
          Url.get_base_name(download) getOrElse
            error("Malformed download URL " + quote(download))
        val archive_path = download_dir + Path.basic(archive_name)

        val platform_dir = component_dir.path + Path.explode(platform.platform_name)
        Isabelle_System.make_directory(platform_dir)

        Isabelle_System.download_file(download, archive_path, progress = progress)
        Isabelle_System.extract(archive_path, platform_dir, strip = true)
        Isabelle_System.copy_file(platform_dir + Path.basic("LICENSE"), platform_dir.expand.dir)
      }
    }


  /* settings */

    component_dir.write_settings("""
if [ -d "$COMPONENT/${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}" ]; then
  ISABELLE_MLTON="$COMPONENT/${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}/bin/mlton"
  case "$ISABELLE_PLATFORM_FAMILY" in
    linux*)
      ISABELLE_MLTON_OPTIONS="-pi-style npi"
      ;;
    *)
      ISABELLE_MLTON_OPTIONS=""
      ;;
  esac
fi
""")


    /* README */

    File.write(component_dir.README,
      """This distribution of MLton has been taken from the TINA project
https://projects.laas.fr/tina/software.php using following downloads:""" +
        platforms.map(_.download(base_url, version)).mkString("\n\n  ", "\n  ", "\n\n") +
"""Some Isabelle platforms are unsupported, notably Windows and Linux ARM.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_mlton", "build component for MLton", Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var base_url = default_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle component_mlton [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")
    -V VERSION   version (default: """" + default_version + """")

  Build component for MLton compiler.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => base_url = arg),
          "V:" -> (arg => version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_mlton(base_url = base_url, version = version, target_dir = target_dir,
          progress = progress)
      })
}
