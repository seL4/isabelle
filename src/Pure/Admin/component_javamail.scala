/*  Title:      Pure/Admin/component_javamail.scala
    Author:     Fabian Huch, TU Muenchen

Build Isabelle java mail component (previously javax-mail, now jakarta + eclipse angus)
from official downloads. See also:

  - https://jakarta.ee/specifications/mail
  - https://mvnrepository.com/artifact/jakarta.mail/jakarta.mail-api

  - https://jakarta.ee/specifications/activation
  - https://mvnrepository.com/artifact/jakarta.activation/jakarta.activation-api

  - https://eclipse-ee4j.github.io/angus-mail/
  - https://mvnrepository.com/artifact/org.eclipse.angus/angus-mail

  - https://eclipse-ee4j.github.io/angus-activation/
  - https://mvnrepository.com/artifact/org.eclipse.angus/angus-activation
*/

package isabelle


object Component_Javamail {
  /* jars */

  sealed case class Jar(group_id: String, artifact_id: String, version: String) {
    override def toString: String = group_id + ":" + artifact_id

    def file_name: String = artifact_id + "-" + version + ".jar"
    def maven_dir: String = group_id.replace('.', '/') + "/" + artifact_id + "/" + version
    def url(repo_url: String): String = repo_url + "/" + maven_dir + "/" + file_name
  }

  val jars =
    List(
      Jar("jakarta.mail", "jakarta.mail-api", "2.1.3"),
      Jar("jakarta.activation", "jakarta.activation-api", "2.1.3"),
      Jar("org.eclipse.angus", "angus-mail", "2.0.3"),
      Jar("org.eclipse.angus", "angus-activation", "2.0.2"))


  /* build javamail */

  val default_download_repo = "https://repo1.maven.org/maven2"

  def build_javamail(
    download_repo: String = default_download_repo,
    progress: Progress = new Progress,
    target_dir: Path = Path.current
  ): Unit = {
    /* component */

    val component_name = "javamail-" + Date.Format.alt_date(Date.now())
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)

    File.write(component_dir.LICENSE, "See the file META-INF/LICENSE.txt in each jar file.")


    /* README */

    File.write(component_dir.README,
      "This is " + component_name + " from\n" + download_repo + """

See also:
  - https://jakarta.ee/specifications/mail
  - https://mvnrepository.com/artifact/jakarta.mail/jakarta.mail-api

  - https://jakarta.ee/specifications/activation
  - https://mvnrepository.com/artifact/jakarta.activation/jakarta.activation-api

  - https://eclipse-ee4j.github.io/angus-mail/
  - https://mvnrepository.com/artifact/org.eclipse.angus/angus-mail

  - https://eclipse-ee4j.github.io/angus-activation/
  - https://mvnrepository.com/artifact/org.eclipse.angus/angus-activation


Fabian
        """ + Date.Format.date(Date.now()) + "\n")


    /* settings */

    val settings = jars.map(jar => "\nclasspath \"$COMPONENT/lib/" + jar.file_name + "\"")
    component_dir.write_settings(settings.mkString)


    /* jars */

    Isabelle_System.make_directory(component_dir.lib)
    for (jar <- jars) {
      val path = component_dir.lib + Path.basic(jar.file_name)
      Isabelle_System.download_file(jar.url(download_repo), path, progress = progress)
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_javamail", "build Isabelle javamail component from official download",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_repo = default_download_repo

        val getopts = Getopts("""
Usage: isabelle component_javamail [OPTIONS] DOWNLOAD

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download repository URL
                 (default: """" + default_download_repo + """")

  Build javamail component from the specified download repository (maven).
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_repo = arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_javamail(download_repo = download_repo, progress = progress, target_dir = target_dir)
      })
}
