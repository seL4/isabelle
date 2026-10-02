/*  Title:      Pure/Admin/component_mlton.scala
    Author:     Makarius

Build Isabelle component for MLton. See also:

  - http://mlton.org
  - https://projects.laas.fr/tina/software.php
*/

package isabelle


object Component_MLton {
  /* platform information */

  sealed case class Download_Platform(platform_name: String, download_name: String)

  val platforms: List[Download_Platform] =
    List(
      Download_Platform("arm64-darwin", "{W}.arm64-darwin.macos-14_gmp-static.tgz"),
      Download_Platform("arm64-linux", "{W}.arm64-linux.ubuntu-22.04-arm_static.tgz"),
      Download_Platform("x86_64-darwin", "{W}.amd64-darwin.macos-13_gmp-static.tgz"),
      Download_Platform("x86_64-linux", "{W}.amd64-linux.ubuntu-20.04_static.tgz"))


  /* build mlton */

  val default_url = "https://github.com/MLton/mlton/releases/download/on-{V}-release"
  val default_version = "20241230"
  val default_variant = "mlton-20241230-1"

  def build_mlton(
    base_url: String = default_url,
    version: String = default_version,
    variant: String = default_variant,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    val component_dir =
      Components.Directory(target_dir + Path.basic(variant)).create(progress = progress)


    /* download executables */

    for (platform <- platforms) {
      Isabelle_System.with_tmp_dir("download") { download_dir =>
        val archive_name = platform.download_name
        val archive_path = download_dir + Path.basic(archive_name)

        val platform_dir = component_dir.path + Path.explode(platform.platform_name)
        Isabelle_System.make_directory(platform_dir)

        val url =
          Url.append_path(base_url, archive_name).replacing("{V}" -> version, "{W}" -> variant)
        Isabelle_System.download_file(url, archive_path, progress = progress)
        Isabelle_System.extract(archive_path, platform_dir, strip = true)
        Isabelle_System.copy_file(platform_dir + Path.basic("LICENSE"), platform_dir.expand.dir)
      }
    }


  /* settings */

    component_dir.write_settings("""
ISABELLE_MLTON_HOME="$COMPONENT"

if [ -d "$ISABELLE_MLTON_HOME/${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}" ]; then
  ISABELLE_MLTON="$ISABELLE_MLTON_HOME/${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}/bin/mlton"
  ISABELLE_MLTON_OPTIONS=""
  case "$ISABELLE_PLATFORM_FAMILY" in
    *_arm)
      ISABELLE_MLTON_NATIVE_OPTIONS=""
      ;;
    *)
      ISABELLE_MLTON_NATIVE_OPTIONS="-codegen native"
      ;;
  esac
fi
""")


    /* README */

    File.write(component_dir.README,
      """This is the MLton SML compiler """ + variant + """ from
https://github.com/MLton/mlton using following downloads:""" +
        platforms.map(_.download_name.replacing("{W}" -> variant)).mkString("\n\n  ", "\n  ", "\n") +
"""
Windows is unsupported.


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
        var variant = default_variant

        val getopts = Getopts("""
Usage: isabelle component_mlton [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")
    -V VERSION   version (default: """" + default_version + """")
    -W VARIANT   variant (default: """" + default_variant + """")

  Build component for MLton compiler.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => base_url = arg),
          "V:" -> (arg => version = arg),
          "W:" -> (arg => variant = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_mlton(base_url = base_url, version = version, variant = variant,
          target_dir = target_dir, progress = progress)
      })
}
