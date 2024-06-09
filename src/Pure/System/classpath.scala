/*  Title:      Pure/System/classpath.scala
    Author:     Makarius

Java classpath and Scala services.
*/

package isabelle


import java.io.{File => JFile}
import java.nio.file.Files
import java.net.URLClassLoader

import scala.jdk.CollectionConverters._


object Classpath {
  abstract class Service
  type Service_Class = Class[Service]

  def apply(
    jar_files: List[JFile] = Nil,
    jar_contents: List[File.Content] = Nil): Classpath =
  {
    val jar_files0 =
      for {
        s <- space_explode(JFile.pathSeparatorChar, System.getProperty("java.class.path", ""))
        if s.nonEmpty
      } yield File.absolute(new JFile(s))

    val jar_files1 =
      jar_files.flatMap(start =>
          File.find_files(start, file => File.is_jar(file.getName)).sortBy(_.getName))
        .map(File.absolute)

    val tmp_jars =
      for (jar <- jar_contents) yield {
        val tmp_jar = Files.createTempFile("jar", "jar").toFile
        tmp_jar.deleteOnExit()
        Bytes.write(tmp_jar, jar.content)
        tmp_jar
      }
    new Classpath(jar_files0 ::: jar_files1, tmp_jars)
  }
}

class Classpath private(static_jars: List[JFile], dynamic_jars: List[JFile]) {
  def jars: List[JFile] = static_jars ::: dynamic_jars
  override def toString: String = jars.mkString("Classpath(", ", ", ")")

  def platform_path: String = jars.map(_.getPath).mkString(JFile.pathSeparator)

  val class_loader: ClassLoader =
  {
    val this_class_loader = this.getClass.getClassLoader
    if (dynamic_jars.isEmpty) this_class_loader
    else {
      val dynamic_jars_url = dynamic_jars.map(file => File.url(file).java_url)
      new URLClassLoader(dynamic_jars_url.toArray, this_class_loader) {
        override def finalize(): Unit = {
          for (jar <- dynamic_jars) {
            try { jar.delete() }
            catch { case _: Throwable => }
          }
        }
      }
    }
  }

  private def init_services(where: String, names: List[String]): List[Classpath.Service_Class] = {
    for (name <- names) yield {
      def err(msg: String): Nothing =
        error("Bad Isabelle/Scala service " + quote(name) + " in " + where + "\n" + msg)
      try { Class.forName(name, true, class_loader).asInstanceOf[Classpath.Service_Class] }
      catch {
        case _: ClassNotFoundException => err("Class not found")
        case exn: Throwable => err(Exn.print(exn))
      }
    }
  }

  val services: List[Classpath.Service_Class] =
  {
    val variable = "ISABELLE_SCALA_SERVICES"
    val services_env =
      init_services(quote(variable), space_explode(':', Isabelle_System.getenv_strict(variable)))
    val services_jars =
      jars.flatMap(jar =>
        init_services(File.standard_path(jar),
          isabelle.setup.Build.get_services(jar.toPath).asScala.toList))
    services_env ::: services_jars
  }

  def make_services[C](c: Class[C]): List[C] =
    for { c1 <- services if Library.is_subclass(c1, c) }
      yield c1.getDeclaredConstructor().newInstance().asInstanceOf[C]
}
