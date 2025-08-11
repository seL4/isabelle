/*  Title:      Pure/Admin/component_jsvg.scala
    Author:     Makarius

Build Isabelle jsvg component from official download.
*/

package isabelle


object Component_JSVG {
  /* build jsvg */

  val default_download_url =
    "https://repo1.maven.org/maven2/com/github/weisj/jsvg/2.0.0/jsvg-2.0.0.jar"

  def build_jsvg(
    download_url: String = default_download_url,
    progress: Progress = new Progress,
    target_dir: Path = Path.current
  ): Unit = {
    val Download_Name = """^.*/([^/]+)\.jar""".r
    val download_name =
      download_url match {
        case Download_Name(download_name) => download_name
        case _ => error("Malformed jar download URL: " + quote(download_url))
      }


    /* component */

    val component_dir =
      Components.Directory(target_dir + Path.basic(download_name)).create(progress = progress)

    File.write(component_dir.LICENSE,
      Url.read("https://raw.githubusercontent.com/weisJ/jsvg/refs/heads/master/LICENSE"))


    /* README */

    File.write(component_dir.README,
      "This is a Java SVG implementation (JSVG) from\n" + download_url +
        "\n\nSee also https://github.com/weisJ/jsvg" +
        "\n\n        Makarius\n        " + Date.Format.date(Date.now()) + "\n")


    /* settings */

    component_dir.write_settings("""
ISABELLE_JSVG_HOME="$COMPONENT"

classpath "$ISABELLE_JSVG_HOME/lib/""" + download_name + """.jar"
""")


    /* jar */

    val jar = component_dir.lib + Path.basic(download_name).jar
    Isabelle_System.make_directory(jar.dir)
    Isabelle_System.download_file(download_url, jar, progress = progress)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_jsvg", "build Isabelle jsvg component from official download",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_download_url

        val getopts = Getopts("""
Usage: isabelle component_jsvg [OPTIONS] DOWNLOAD

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL
                 (default: """" + default_download_url + """")

  Build jsvg component from the specified download URL (JAR).
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_jsvg(download_url = download_url, progress = progress, target_dir = target_dir)
      })
}
