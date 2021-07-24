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
  type Context = isabelle.setup.Build.Context

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

    new isabelle.setup.Build.Context(dir.java_path, props, props_path.implode)
  }

  def build(dir: Path,
    fresh: Boolean = false,
    component: Boolean = false,
    more_props: Properties.T = Nil): Unit =
  {
    isabelle.setup.Build.build(
      context(dir, component = component, more_props = more_props), fresh)
  }

  def component_contexts(): List[Context] =
    isabelle.setup.Build.component_contexts().asScala.toList
}
