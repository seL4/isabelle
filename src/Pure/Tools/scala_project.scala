/*  Title:      Pure/Tools/scala_project.scala
    Author:     Makarius

Manage Isabelle/Scala/Java project sources, with output to Maven for
IntelliJ IDEA.
*/

package isabelle


object Scala_Project
{
  /* Maven project */

  def java_version: String = "11"
  def scala_version: String = scala.util.Properties.versionNumberString

  def maven_project(jars: List[Path]): String =
  {
    def dependency(jar: Path): String =
    {
      val name = jar.expand.drop_ext.base.implode
      val system_path = File.platform_path(jar.absolute)
      """  <dependency>
    <groupId>classpath</groupId>
    <artifactId>""" + XML.text(name) + """</artifactId>
    <version>0</version>
    <scope>system</scope>
    <systemPath>""" + XML.text(system_path) + """</systemPath>
  </dependency>"""
    }

    """<?xml version="1.0" encoding="UTF-8"?>
<project xmlns="http://maven.apache.org/POM/4.0.0" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xsi:schemaLocation="http://maven.apache.org/POM/4.0.0 http://maven.apache.org/xsd/maven-4.0.0.xsd">
  <modelVersion>4.0.0</modelVersion>

  <groupId>isabelle</groupId>
  <artifactId>isabelle</artifactId>
  <version>0</version>

  <properties>
    <project.build.sourceEncoding>UTF-8</project.build.sourceEncoding>
    <maven.compiler.source>""" + java_version + """</maven.compiler.source>
    <maven.compiler.target>""" + java_version + """</maven.compiler.target>
  </properties>

  <build>
    <plugins>
      <plugin>
        <groupId>net.alchim31.maven</groupId>
        <artifactId>scala-maven-plugin</artifactId>
        <version>4.5.3</version>
        <configuration>
            <scalaVersion>""" + scala_version + """</scalaVersion>
        </configuration>
        </plugin>
    </plugins>
  </build>

  <dependencies>""" + jars.map(dependency).mkString("\n", "\n", "\n") + """</dependencies>
</project>"""
  }


  /* plugins: modules with dynamic build */

  class Plugin(dir: Path) extends Isabelle_System.Service
  {
    def context(): Scala_Build.Context = Scala_Build.context(dir)
  }

  lazy val plugins: List[Plugin] = Isabelle_System.make_services(classOf[Plugin])


  /* file and directories */

  lazy val isabelle_files: (List[Path], List[Path]) =
  {
    val contexts = Scala_Build.component_contexts() ::: plugins.map(_.context())

    val jars1 = Path.split(Isabelle_System.getenv("ISABELLE_CLASSPATH"))
    val jars2 = contexts.flatMap(_.requirements)

    val jars =
      Library.distinct(jars1 ::: jars2).filterNot(path => contexts.exists(_.is_module(path)))

    val sources =
      (for {
        context <- contexts.iterator
        path <- context.sources.iterator
        if path.is_scala || path.is_java
      } yield path).toList

    (jars, sources)
  }

  lazy val isabelle_scala_files: Map[String, Path] =
  {
    val context = Scala_Build.context(Path.ISABELLE_HOME, component = true)
    context.sources.iterator.foldLeft(Map.empty[String, Path]) {
      case (map, path) =>
        if (path.is_scala) {
        val base = path.base.implode
          map.get(base) match {
            case None => map + (base -> path)
            case Some(path2) => error("Conflicting base names: " + path + " vs. " + path2)
          }
        }
        else map
    }
  }


  /* compile-time position */

  def here: Here =
  {
    val exn = new Exception
    exn.getStackTrace.toList match {
      case _ :: caller :: _ =>
        val name = proper_string(caller.getFileName).getOrElse("")
        val line = caller.getLineNumber
        new Here(name, line)
      case _ => new Here("", 0)
    }
  }

  class Here private[Scala_Project](name: String, line: Int)
  {
    override def toString: String = name + ":" + line
    def position: Position.T =
      isabelle_scala_files.get(name) match {
        case Some(path) => Position.Line_File(line, path.implode)
        case None => Position.none
      }
  }


  /* scala project */

  val default_project_dir = Path.explode("$ISABELLE_HOME_USER/scala_project")

  def package_name(source_file: Path): Option[String] =
  {
    val lines = split_lines(File.read(source_file))
    val Package = """\s*\bpackage\b\s*(?:object\b\s*)?((?:\w|\.)+)\b.*""".r
    lines.collectFirst({ case Package(name) => name })
  }

  def the_package_dir(source_file: Path): Path =
  {
    package_name(source_file) match {
      case Some(name) =>
        if (source_file.is_java) Path.explode(space_explode('.', name).mkString("/"))
        else Path.basic(name)
      case None => error("Failed to guess package from " + source_file)
    }
  }

  def scala_project(
    project_dir: Path = default_project_dir,
    more_sources: List[Path] = Nil,
    symlinks: Boolean = false,
    force: Boolean = false,
    progress: Progress = new Progress): Unit =
  {
    if (project_dir.file.exists) {
      val detect =
        project_dir.is_dir &&
        (project_dir + Path.explode("pom.xml")).is_file &&
        (project_dir + Path.explode("src/main/scala")).is_dir

      if (force && detect) {
        progress.echo("Purging existing project directory: " + project_dir.absolute)
        Isabelle_System.rm_tree(project_dir)
      }
      else error("Project directory already exists: " + project_dir.absolute)
    }

    progress.echo("Creating project directory: " + project_dir.absolute)
    Isabelle_System.make_directory(project_dir)

    val java_src_dir = Isabelle_System.make_directory(Path.explode("src/main/java"))
    val scala_src_dir = Isabelle_System.make_directory(Path.explode("src/main/scala"))

    val (jars, sources) = isabelle_files
    isabelle_scala_files

    File.write(project_dir + Path.explode("pom.xml"), maven_project(jars))

    for (source <- sources ::: more_sources) {
      val dir = (if (source.is_java) java_src_dir else scala_src_dir) + the_package_dir(source)
      val target_dir = project_dir + dir
      if (!target_dir.is_dir) {
        progress.echo("  Creating package directory: " + dir)
        Isabelle_System.make_directory(target_dir)
      }
      if (symlinks) Isabelle_System.symlink(source.absolute, target_dir, native = true)
      else Isabelle_System.copy_file(source, target_dir)
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("scala_project", "setup Maven project for Isabelle/Scala/jEdit",
      Scala_Project.here, args =>
    {
      var project_dir = default_project_dir
      var symlinks = false
      var force = false

      val getopts = Getopts("""
Usage: isabelle scala_project [OPTIONS] [MORE_SOURCES ...]

  Options are:
    -D DIR       project directory (default: """ + default_project_dir + """)
    -L           make symlinks to original source files
    -f           force update of existing directory

  Setup Maven project for Isabelle/Scala/jEdit --- to support common IDEs
  such as IntelliJ IDEA.
""",
        "D:" -> (arg => project_dir = Path.explode(arg)),
        "L" -> (_ => symlinks = true),
        "f" -> (_ => force = true))

      val more_args = getopts(args)

      val more_sources = more_args.map(Path.explode)
      val progress = new Console_Progress

      scala_project(project_dir = project_dir, more_sources = more_sources,
        symlinks = symlinks, force = force, progress = progress)
    })
}
