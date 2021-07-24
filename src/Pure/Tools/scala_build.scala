/*  Title:      Pure/Tools/scala_build.scala
    Author:     Makarius

Manage and build Isabelle/Scala/Java components.
*/

package isabelle


import java.util.{Properties => JProperties}
import java.nio.file.Files

import scala.jdk.CollectionConverters._


object Scala_Build
{
  class Context private[Scala_Build](java_context: isabelle.setup.Build.Context)
  {
    def is_module(path: Path): Boolean =
    {
      val module_name: String = java_context.module_name()
      module_name.nonEmpty && File.eq(java_context.path(module_name).toFile, path.file)
    }

    def sources: List[Path] =
      java_context.sources().asScala.toList.map(s => File.path(java_context.path(s).toFile))

    def requirements: List[Path] =
      (for {
        s <- java_context.requirements().asScala.iterator
        p <- java_context.requirement_paths(s).asScala.iterator
      } yield (File.path(p.toFile))).toList

    def build(fresh: Boolean = false): Unit =
      isabelle.setup.Build.build(java_context, fresh)
  }

  def context(dir: Path,
    component: Boolean = false,
    more_props: Properties.T = Nil): Context =
  {
    val props_name =
      if (component) isabelle.setup.Build.COMPONENT_BUILD_PROPS
      else isabelle.setup.Build.BUILD_PROPS
    val props_path = dir + Path.explode(props_name)

    val props = new JProperties
    props.load(Files.newBufferedReader(props_path.java_path))
    for ((a, b) <- more_props) props.put(a, b)

    new Context(new isabelle.setup.Build.Context(dir.java_path, props, props_path.implode))
  }

  def build(dir: Path,
    fresh: Boolean = false,
    component: Boolean = false,
    more_props: Properties.T = Nil): Unit =
  {
    context(dir, component = component, more_props = more_props).build(fresh = fresh)
  }

  def component_contexts(): List[Context] =
    isabelle.setup.Build.component_contexts().asScala.toList.map(new Context(_))
}
