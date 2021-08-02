/*  Title:      Pure/Tools/scala_project.scala
    Author:     Makarius

Manage Isabelle/Scala/Java project sources, with output to Gradle for
IntelliJ IDEA.
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

  def plugin_contexts(): List[Scala_Build.Context] =
    for (plugin <- List("jedit_base", "jedit_main"))
    yield Scala_Build.context(Path.explode("$ISABELLE_HOME/src/Tools/jEdit") + Path.basic(plugin))

  lazy val isabelle_files: (List[Path], List[Path]) =
  {
    val contexts = Scala_Build.component_contexts() ::: plugin_contexts()

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

  def package_dir(source_file: Path): Option[Path] =
  {
    val lines = split_lines(File.read(source_file))
    val Package = """\s*\bpackage\b\s*(?:object\b\s*)?((?:\w|\.)+)\b.*""".r
    lines.collectFirst(
      {
        case Package(name) =>
          if (source_file.is_java) Path.explode(space_explode('.', name).mkString("/"))
          else Path.basic(name)
      })
  }

  def the_package_dir(source_file: Path): Path =
    package_dir(source_file) getOrElse error("Failed to guess package from " + source_file)

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
        (project_dir + Path.explode("build.gradle")).is_file &&
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
  compileOnly files(
    """ + jars.map(jar => groovy_string(File.platform_path(jar))).mkString("", ",\n    ", ")") +
"""
}
""")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("scala_project", "setup Gradle project for Isabelle/Scala/jEdit",
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

  Setup Gradle project for Isabelle/Scala/jEdit --- to support Scala IDEs
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
