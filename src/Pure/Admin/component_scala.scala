/*  Title:      Pure/Admin/component_scala.scala
    Author:     Makarius

Build Isabelle Scala component from official downloads.
*/

package isabelle


object Component_Scala {
  /* downloads */

  sealed case class Download(
    name: String,
    version: String,
    url: String,
    physical_url: String = "",
    base_version: String = "3"
  ) {
    def make_url(template: String): String =
      template.replace("{V}", version).replace("{B}", base_version)

    def proper_url: String = make_url(proper_string(physical_url).getOrElse(url))

    def artifact: String =
      Library.take_suffix[Char](_ != '/', proper_url.toList)._2.mkString

    def get(path: Path, progress: Progress = new Progress): Unit =
      Isabelle_System.download_file(proper_url, path, progress = progress)

    def print: String =
      "  * " + name + " " + version + if_proper(base_version, " for Scala " + base_version) +
        ":\n    " + make_url(url)
  }

  val main_download: Download =
    Download("scala", "3.4.1", base_version = "",
      url = "https://github.com/lampepfl/dotty/releases/download/{V}/scala3-{V}.tar.gz")

  val lib_downloads: List[Download] = List(
    Download("scala-parallel-collections", "1.0.4",
      "https://mvnrepository.com/artifact/org.scala-lang.modules/scala-parallel-collections_{B}/{V}",
      physical_url = "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-parallel-collections_{B}/{V}/scala-parallel-collections_{B}-{V}.jar"),
    Download("scala-parser-combinators", "2.3.0",
      "https://mvnrepository.com/artifact/org.scala-lang.modules/scala-parser-combinators_{B}/{V}",
      physical_url = "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-parser-combinators_{B}/{V}/scala-parser-combinators_{B}-{V}.jar"),
    Download("scala-swing", "3.0.0",
      "https://mvnrepository.com/artifact/org.scala-lang.modules/scala-swing_{B}/{V}",
      physical_url = "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-swing_{B}/{V}/scala-swing_{B}-{V}.jar"),
    Download("scala-xml", "2.2.0",
      "https://mvnrepository.com/artifact/org.scala-lang.modules/scala-xml_{B}/{V}",
      physical_url = "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-xml_{B}/{V}/scala-xml_{B}-{V}.jar")
  )


  /* build Scala component */

  def build_scala(
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    /* component */

    val component_name = main_download.name + "-" + main_download.version
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)


    /* download */

    Isabelle_System.with_tmp_file("archive", ext = "tar.gz") { archive_path =>
      main_download.get(archive_path, progress = progress)
      Isabelle_System.extract(archive_path, component_dir.path, strip = true)
    }

    lib_downloads.foreach(download =>
      download.get(component_dir.lib + Path.basic(download.artifact), progress = progress))

    File.write(component_dir.LICENSE,
      Url.read("https://www.apache.org/licenses/LICENSE-2.0.txt"))


    /* classpath */

    val classpath: List[String] = {
      def no_function(name: String): String = "function " + name + "() {\n:\n}"
      val script =
        cat_lines(List(
          no_function("stty"),
          no_function("tput"),
          "PROG_HOME=" + File.bash_path(component_dir.path),
          File.read(component_dir.path + Path.explode("bin/common"))
            .replace("scala_exit_status=127", "scala_exit_status=0"),
          "compilerJavaClasspathArgs",
          "echo \"$jvm_cp_args\""))

      val main_classpath = Path.split(Isabelle_System.bash(script).check.out).map(_.file_name)
      val lib_classpath = lib_downloads.map(_.artifact)

      main_classpath ::: lib_classpath
    }

    val interfaces =
      classpath.find(_.startsWith("scala3-interfaces"))
        .getOrElse(error("Missing jar for scala3-interfaces"))


    /* settings */

    component_dir.write_settings("""
SCALA_HOME="$COMPONENT"
SCALA_INTERFACES="$SCALA_HOME/lib/""" + interfaces + """"
""" + terminate_lines(classpath.map(jar => "classpath \"$SCALA_HOME/lib/" + jar + "\"")))


    /* adhoc changes */

    val patched_scripts = List("bin/scala", "bin/scalac")
    for (name <- patched_scripts) {
      File.change(component_dir.path + Path.explode(name)) {
        _.replace(""""-Dscala.home=$PROG_HOME"""", """"-Dscala.home=\"$PROG_HOME\""""")
      }
    }


    /* README */

    File.write(component_dir.README,
      "This distribution of Scala integrates the following parts:\n\n" +
      (main_download :: lib_downloads).map(_.print).mkString("\n\n") + """

Minor changes to """ + patched_scripts.mkString(" and ") + """ allow an installation location
with spaces in the directory name.


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_scala", "build Isabelle Scala component from official downloads",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current

        val getopts = Getopts("""
Usage: isabelle component_scala [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")

  Build Isabelle Scala component from official downloads.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_scala(target_dir = target_dir, progress = progress)
      })
}
