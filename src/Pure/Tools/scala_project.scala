/*  Title:      Pure/Tools/scala_project.scala
    Author:     Makarius

Manage Isabelle/Scala/Java project sources, with output to Gradle for
IntelliJ IDEA.
*/

package isabelle

import scala.jdk.CollectionConverters._


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

  def plugin_contexts(): List[isabelle.setup.Build.Context] =
    for (plugin <- List("jedit_base", "jedit_main"))
    yield {
      val dir = Path.explode("$ISABELLE_HOME/src/Tools/jEdit") + Path.basic(plugin)
      isabelle.setup.Build.directory_context(dir.java_path)
    }

  lazy val isabelle_files: (List[Path], List[Path]) =
  {
    val contexts =
      isabelle.setup.Build.component_contexts().asScala.toList :::
        plugin_contexts()

    val jars1 = Path.split(Isabelle_System.getenv("ISABELLE_CLASSPATH"))
    val jars2 =
      (for {
        context <- contexts.iterator
        s <- context.requirements().asScala.iterator
        path <- context.requirement_paths(s).asScala.iterator
      } yield File.path(path.toFile)).toList

    val jar_files =
      Library.distinct(jars1 ::: jars2).filterNot(path =>
        contexts.exists(context =>
        {
          val name: String = context.module_name()
          name.nonEmpty && File.eq(context.path(name).toFile, path.file)
        }))

    val source_files =
      (for {
        context <- contexts.iterator
        file <- context.sources.asScala.iterator
        if file.endsWith(".scala") || file.endsWith(".java")
      } yield File.path(context.path(file).toFile)).toList

    (jar_files, source_files)
  }

  lazy val isabelle_scala_files: Map[String, Path] =
  {
    val context = isabelle.setup.Build.component_context(Path.ISABELLE_HOME.java_path)
    context.sources().asScala.iterator.foldLeft(Map.empty[String, Path]) {
      case (map, name) =>
        if (name.endsWith(".scala")) {
        val path = File.path(context.path(name).toFile)
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

  def package_dir(source_file: Path): Option[Path] =
  {
    val is_java = source_file.file_name.endsWith(".java")
    val lines = split_lines(File.read(source_file))
    val Package = """\s*\bpackage\b\s*(?:object\b\s*)?((?:\w|\.)+)\b.*""".r
    lines.collectFirst(
      {
        case Package(name) =>
          if (is_java) Path.explode(space_explode('.', name).mkString("/"))
          else Path.basic(name)
      })
  }

  def the_package_dir(source_file: Path): Path =
    package_dir(source_file) getOrElse error("Failed to guess package from " + source_file)

  def scala_project(project_dir: Path, symlinks: Boolean = false): Unit =
  {
    if (symlinks && Platform.is_windows)
      error("Cannot create symlinks on Windows")

    if (project_dir.is_file || project_dir.is_dir)
      error("Project directory already exists: " + project_dir)

    val java_src_dir = Isabelle_System.make_directory(project_dir + Path.explode("src/main/java"))
    val scala_src_dir = Isabelle_System.make_directory(project_dir + Path.explode("src/main/scala"))

    val (jar_files, source_files) = isabelle_files
    isabelle_scala_files

    for (source <- source_files) {
      val dir = if (source.file_name.endsWith(".java")) java_src_dir else scala_src_dir
      val target = dir + the_package_dir(source)
      Isabelle_System.make_directory(target)
      if (symlinks) Isabelle_System.symlink(source, target)
      else Isabelle_System.copy_file(source, target)
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
    """ + jar_files.map(jar => groovy_string(File.platform_path(jar))).mkString("", ",\n    ", ")") +
"""
}
""")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("scala_project", "setup Gradle project for Isabelle/Scala/jEdit",
      Scala_Project.here, args =>
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
