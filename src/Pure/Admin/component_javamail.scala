/*  Title:      Pure/Admin/component_javamail.scala
    Author:     Fabian Huch, TU Muenchen

Build Isabelle javax-mail component from official download. See also:

  - https://javaee.github.io/javamail/
  - https://mvnrepository.com/artifact/javax.mail/mail
*/

package isabelle


object Component_Javamail {
  /* build javamail */

  val default_download_url =
    "https://repo1.maven.org/maven2/javax/mail/mail/1.4.7/mail-1.4.7.jar"

  def build_javamail(
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
    val component_name = "java" + download_name


    /* component */

    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)

    File.write(component_dir.LICENSE,
      Url.read("https://raw.githubusercontent.com/javaee/javamail/master/LICENSE.txt"))


    /* README */

    File.write(component_dir.README,
      "This is " + component_name + " from\n" + download_url +
        "\n\nSee also https://javaee.github.io/javamail and https://mvnrepository.com/artifact/javax.mail/mail" +
        "\n\n        Fabian\n        " + Date.Format.date(Date.now()) + "\n")


    /* settings */

    component_dir.write_settings("""
classpath "$COMPONENT/lib/""" + download_name + """.jar"
""")


    /* jar */

    val jar = component_dir.lib + Path.basic(download_name).jar
    Isabelle_System.make_directory(jar.dir)
    Isabelle_System.download_file(download_url, jar, progress = progress)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_javamail", "build Isabelle javamail component from official download",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_download_url

        val getopts = Getopts("""
Usage: isabelle component_javamail [OPTIONS] DOWNLOAD

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL
                 (default: """" + default_download_url + """")

  Build javamail component from the specified download URL (JAR).
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_javamail(download_url = download_url, progress = progress, target_dir = target_dir)
      })
}
