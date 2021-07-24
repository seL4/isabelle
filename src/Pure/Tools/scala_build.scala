/*  Title:      Pure/Tools/scala_build.scala
    Author:     Makarius

Manage and build Isabelle/Scala/Java components.
*/

package isabelle


import java.util.{Properties => JProperties}
import java.io.{ByteArrayOutputStream, PrintStream}
import java.nio.file.Files

import scala.jdk.CollectionConverters._


object Scala_Build
{
  class Context private[Scala_Build](java_context: isabelle.setup.Build.Context)
  {
    override def toString: String = java_context.toString

    def is_module(path: Path): Boolean =
    {
      val module_name = java_context.module_name()
      module_name.nonEmpty && File.eq(java_context.path(module_name).toFile, path.file)
    }

    def module_result: Option[Path] =
    {
      java_context.module_result() match {
        case "" => None
        case module => Some(File.path(java_context.path(module).toFile))
      }
    }

    def sources: List[Path] =
      java_context.sources().asScala.toList.map(s => File.path(java_context.path(s).toFile))

    def requirements: List[Path] =
      (for {
        s <- java_context.requirements().asScala.iterator
        p <- java_context.requirement_paths(s).asScala.iterator
      } yield (File.path(p.toFile))).toList

    def build(fresh: Boolean = false): String =
    {
      val output0 = new ByteArrayOutputStream
      val output = new PrintStream(output0)
      def get_output(): String =
      {
        output.flush()
        Library.trim_line(output0.toString(UTF8.charset))
      }
      try {
        Console.withOut(output) {
          Console.withErr(output) {
            isabelle.setup.Build.build(output, java_context, fresh)
          }
        }
        get_output()
      }
      catch { case ERROR(msg) => cat_error(get_output(), msg) }
    }
  }

  def context(dir: Path,
    component: Boolean = false,
    no_title: Boolean = false,
    do_build: Boolean = false,
    module: Option[Path] = None): Context =
  {
    val props_name =
      if (component) isabelle.setup.Build.COMPONENT_BUILD_PROPS
      else isabelle.setup.Build.BUILD_PROPS
    val props_path = dir + Path.explode(props_name)

    val props = new JProperties
    props.load(Files.newBufferedReader(props_path.java_path))
    if (no_title) props.remove(isabelle.setup.Build.TITLE)
    if (do_build) props.remove(isabelle.setup.Build.NO_BUILD)
    if (module.isDefined) props.put(isabelle.setup.Build.MODULE, File.standard_path(module.get))

    new Context(new isabelle.setup.Build.Context(dir.java_path, props, props_path.implode))
  }

  def build(dir: Path,
    fresh: Boolean = false,
    component: Boolean = false,
    no_title: Boolean = false,
    do_build: Boolean = false,
    module: Option[Path] = None): String =
  {
    context(dir, component = component, no_title = no_title, do_build = do_build, module = module)
      .build(fresh = fresh)
  }

  sealed case class Result(output: String, jar_bytes: Bytes, jar_path: Option[Path])
  {
    def write(): Unit =
    {
      if (jar_path.isDefined) {
        Isabelle_System.make_directory(jar_path.get.dir)
        Bytes.write(jar_path.get, jar_bytes)
      }
    }
  }

  def build_result(dir: Path, component: Boolean = false): Result =
  {
    Isabelle_System.with_tmp_file("result", "jar")(tmp_file =>
    {
      val output =
        build(dir, component = component, no_title = true, do_build = true, module = Some(tmp_file))
      val jar_bytes = Bytes.read(tmp_file)
      val jar_path = context(dir, component = component).module_result
      Result(output, jar_bytes, jar_path)
    })
  }

  def component_contexts(): List[Context] =
    isabelle.setup.Build.component_contexts().asScala.toList.map(new Context(_))
}
