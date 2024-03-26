/*  Title:      Pure/Admin/component_go.scala
    Author:     Makarius

Build Isabelle component for Go: https://go.dev
*/

package isabelle


object Component_Go {
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


  /* build go */

  val default_url = "https://go.dev/dl"
  val default_version = "1.22.1"

  def build_go(
    base_url: String = default_url,
    version: String = default_version,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    val component_dir =
      Components.Directory(target_dir + Path.basic("go-" + version)).create(progress = progress)


    /* download */

    Isabelle_System.with_tmp_dir("download") { download_dir =>
      for (platform <- all_platforms.reverse) {
        val download = platform.download(base_url, version)

        val archive_name =
          Url.get_base_name(download) getOrElse
            error("Malformed download URL " + quote(download))
        val archive_path = download_dir + Path.basic(archive_name)

        Isabelle_System.download_file(download, archive_path, progress = progress)
        Isabelle_System.extract(archive_path, component_dir.path, strip = true)

        val platform_dir = component_dir.path + platform.path
        Isabelle_System.move_file(component_dir.bin, platform_dir)
      }
    }

    File.find_files(component_dir.path.file, pred = file => File.is_exe(file.getName)).
      foreach(file => File.set_executable(File.path(file)))


    /* isabelle tool */

    val isabelle_tool_dir = component_dir.path + Path.explode("isabelle_tool")
    Isabelle_System.make_directory(isabelle_tool_dir)

    for (tool <- List("go", "gofmt")) {
      val isabelle_tool = isabelle_tool_dir + Path.basic(tool)
      File.write(isabelle_tool,
"""#!/usr/bin/env bash
#
# Author: Makarius
#
# DESCRIPTION: invoke """ + tool + """ within the Isabelle environment

export GOROOT="$ISABELLE_GOROOT"
exec "$ISABELLE_GOEXE/""" + tool + """" "$@"
""")
      File.set_executable(isabelle_tool)
    }


    /* settings */

    component_dir.write_settings("""
ISABELLE_GOROOT="$COMPONENT"
ISABELLE_GOEXE="$ISABELLE_GOROOT/${ISABELLE_WINDOWS_PLATFORM64:-${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}}"

ISABELLE_TOOLS="$ISABELLE_TOOLS:$ISABELLE_GOROOT/isabelle_tool"
""")


    /* platform.props */

    File.write(component_dir.platform_props,
      (for ((a, b) <- all_platforms.groupBy(_.family_name).iterator)
        yield a + " = " + b.flatMap(_.paths).mkString(" ")
      ).mkString("", "\n", "\n"))


    /* README */

    File.write(component_dir.README,
      """This distribution of Go has been assembled from official downloads from
""" + base_url + """


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_go", "build component for Go", Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var base_url = default_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle component_go [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL (default: """" + default_url + """")
    -V VERSION   version (default: """" + default_version + """")

  Build component for Go development environment.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => base_url = arg),
          "V:" -> (arg => version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_go(base_url = base_url, version = version, target_dir = target_dir,
          progress = progress)
      })
}
