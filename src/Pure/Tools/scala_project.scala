/*  Title:      Pure/Tools/scala_project.scala
    Author:     Makarius

Setup Gradle project for Isabelle/Scala/jEdit.
*/

package isabelle


object Scala_Project
{
  /* groovy syntax */

  def groovy_string(s: String): String =
  {
    s.map(c =>
      c match {
        case '\t' | '\b' | '\n' | '\r' | '\f' | '\\' | '\'' | '"' => "\\" + c
        case _ => c.toString
      }).mkString("'", "", "'")
  }


  /* file and directories */

  def isabelle_files(): List[String] =
  {
    val files1 =
    {
      val isabelle_home = Path.explode("~~").canonical
      Path.split(Isabelle_System.getenv("ISABELLE_CLASSPATH")).
        map(path => File.relative_path(isabelle_home, path).getOrElse(path).implode)
    }

    val files2 =
      (for {
        path <-
          List(
            Path.explode("~~/lib/classes/Pure.shasum"),
            Path.explode("~~/src/Tools/jEdit/dist/Isabelle-jEdit.shasum"))
        line <- Library.trim_split_lines(File.read(path))
        name =
          if (line.length > 42 && line(41) == '*') line.substring(42)
          else error("Bad shasum entry: " + quote(line))
        if name != "lib/classes/Pure.jar" &&
          name != "src/Tools/jEdit/dist/jedit.jar" &&
          name != "src/Tools/jEdit/dist/jars/Isabelle-jEdit-base.jar" &&
          name != "src/Tools/jEdit/dist/jars/Isabelle-jEdit.jar"
      } yield name)

    files1 ::: files2
  }

  val isabelle_dirs: List[(String, Path)] =
    List(
      "src/Pure/" -> Path.explode("isabelle"),
      "src/Tools/Graphview/" -> Path.explode("isabelle.graphview"),
      "src/Tools/VSCode/" -> Path.explode("isabelle.vscode"),
      "src/Tools/jEdit/src-base/" -> Path.explode("isabelle.jedit_base"),
      "src/Tools/jEdit/src/" -> Path.explode("isabelle.jedit"),
      "src/HOL/SPARK/Tools" -> Path.explode("isabelle.spark"),
      "src/HOL/Tools/Nitpick" -> Path.explode("isabelle.nitpick"))


  /* scala project */

  def scala_project(project_dir: Path, symlinks: Boolean = false)
  {
    if (symlinks && Platform.is_windows)
      error("Cannot create symlinks on Windows")

    if (project_dir.is_file || project_dir.is_dir)
      error("Project directory already exists: " + project_dir)

    val src_dir = project_dir + Path.explode("src/main/scala")
    val java_src_dir = project_dir + Path.explode("src/main/java")
    val scala_src_dir = Isabelle_System.make_directory(project_dir + Path.explode("src/main/scala"))

    Isabelle_System.copy_dir(Path.explode("~~/src/Tools/jEdit/dist/jEdit"), java_src_dir)

    val files = isabelle_files()

    for (file <- files if file.endsWith(".scala")) {
      val (path, target) =
        isabelle_dirs.collectFirst({
          case (prfx, p) if file.startsWith(prfx) =>
            (Path.explode("~~") + Path.explode(file), scala_src_dir + p)
        }).getOrElse(error("Unknown directory prefix for " + quote(file)))

      Isabelle_System.make_directory(target)
      if (symlinks) File.link(path, target) else File.copy(path, target)
    }

    val jars =
      for (file <- files if file.endsWith(".jar"))
      yield {
        if (file.startsWith("/")) file
        else Isabelle_System.getenv("ISABELLE_HOME") + "/" + file
      }

    File.write(project_dir + Path.explode("settings.gradle"), "rootProject.name = 'Isabelle'\n")
    File.write(project_dir + Path.explode("build.gradle"),
"""plugins {
  id 'scala'
}

repositories {
  mavenCentral()
}

dependencies {
  implementation 'org.scala-lang:scala-library:""" + scala.util.Properties.versionNumberString + """'
  compile files(
    """ + jars.map(jar => groovy_string(File.platform_path(jar))).mkString("", ",\n    ", ")") +
"""
}
""")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("scala_project", "setup Gradle project for Isabelle/Scala/jEdit", args =>
    {
      var symlinks = false

      val getopts = Getopts("""
Usage: isabelle scala_project [OPTIONS] PROJECT_DIR

  Options are:
    -L           make symlinks to original scala files

  Setup Gradle project for Isabelle/Scala/jEdit --- to support Scala IDEs
  such as IntelliJ IDEA.
""",
        "L" -> (_ => symlinks = true))

      val more_args = getopts(args)

      val project_dir =
        more_args match {
          case List(dir) => Path.explode(dir)
          case _ => getopts.usage()
        }

      scala_project(project_dir, symlinks = symlinks)
    })
}
