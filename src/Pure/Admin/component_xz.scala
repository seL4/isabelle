/*  Title:      Pure/Admin/component_xz.scala
    Author:     Makarius

Build Isabelle xz-java component from official download.
*/

package isabelle


object Component_XZ {
  /* build xz */

  val main_url = "https://tukaani.org/xz/java.html"
  val default_source_url = "https://github.com/tukaani-project/xz-java/releases/download"
  val default_download_url = "https://repo1.maven.org/maven2/org/tukaani/xz"
  val default_version = "1.10"

  def build_xz(
    target_dir: Path = Path.current,
    source_url: String = default_source_url,
    download_url: String = default_download_url,
    version: String = default_version,
    progress: Progress = new Progress,
  ): Unit = {
    /* component */

    val component_name = "xz-java-" + version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)

    File.write(component_dir.README,
      "This is " + component_name + " from " + main_url +
        "\n\n        Makarius\n        " + Date.Format.date(Date.now()) + "\n")

    Isabelle_System.with_tmp_file("tmp", ext = "zip") { tmp =>
      Isabelle_System.download_file(
        source_url + "/v" + version + "/xz-java-" + version + ".zip", tmp, progress = progress)
      Isabelle_System.extract(tmp, component_dir.path)
    }


    /* lib */

    val jar_name = "xz-" + version + ".jar"

    Isabelle_System.make_directory(component_dir.lib)
    Isabelle_System.download_file(
      download_url + "/" + version + "/" + jar_name,
      component_dir.lib + Path.basic(jar_name), progress = progress)


    /* settings */

    component_dir.write_settings("""
ISABELLE_XZ_HOME="$COMPONENT"

classpath "$ISABELLE_XZ_HOME/lib/""" + jar_name + """"
""")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_xz", "build Isabelle xz-java component from official download",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var source_url = default_source_url
        var download_url = default_download_url
        var version = default_version

        val getopts = Getopts("""
Usage: isabelle component_xz [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -S URL       source URL (default: """ + quote(default_source_url) + """)
    -U URL       download URL (default: """ + quote(default_download_url) + """)
    -V VERSION   version (default: """ + quote(default_version) + """)

  Build zxz-java component from the specified download base URL and VERSION,
  see also """ + main_url + "\n",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "S:" -> (arg => source_url = arg),
          "U:" -> (arg => download_url = arg),
          "V:" -> (arg => version = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_xz(target_dir = target_dir, source_url = source_url,
          download_url = download_url, version = version, progress = progress)
      })
}
