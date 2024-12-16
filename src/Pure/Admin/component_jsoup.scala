/*  Title:      Pure/Admin/component_jsoup.scala
    Author:     Makarius

Build Isabelle jsoup component from official download.
*/

package isabelle


object Component_Jsoup {
  /* build jsoup */

  val default_download_url =
    "https://repo1.maven.org/maven2/org/jsoup/jsoup/1.18.3/jsoup-1.18.3.jar"

  def build_jsoup(
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
      Url.read("https://raw.githubusercontent.com/jhy/jsoup/master/LICENSE"))


    /* README */

    File.write(component_dir.README,
      "This is " + download_name + " from\n" + download_url +
        "\n\nSee also https://jsoup.org and https://github.com/jhy/jsoup" +
        "\n\n        Makarius\n        " + Date.Format.date(Date.now()) + "\n")


    /* settings */

    component_dir.write_settings("""
ISABELLE_JSOUP_HOME="$COMPONENT"

classpath "$ISABELLE_JSOUP_HOME/lib/""" + download_name + """.jar"
""")


    /* jar */

    val jar = component_dir.lib + Path.basic(download_name).jar
    Isabelle_System.make_directory(jar.dir)
    Isabelle_System.download_file(download_url, jar, progress = progress)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_jsoup", "build Isabelle jsoup component from official download",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_download_url

        val getopts = Getopts("""
Usage: isabelle component_jsoup [OPTIONS] DOWNLOAD

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL
                 (default: """" + default_download_url + """")

  Build jsoup component from the specified download URL (JAR).
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_jsoup(download_url = download_url, progress = progress, target_dir = target_dir)
      })
}
