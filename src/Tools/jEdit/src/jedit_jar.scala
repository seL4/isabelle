/*  Title:      Tools/jEdit/src/jedit_jar.scala
    Author:     Makarius

Offline access to jEdit jar resources.
*/

package isabelle.jedit


import isabelle._


object JEdit_JAR {
  /* jEdit jar resources */

  def get_resource(name: String): String = {
    val s = classOf[org.gjt.sp.jedit.jEdit].getResourceAsStream(name)
    if (s == null) error("Bad jEdit resource: " + quote(name))
    else using(s)(File.read_stream)
  }

  object JEdit_Resource extends Scala.Fun_Strings("jEdit.resource") {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] = args.map(get_resource)
  }

  class Scala_Functions extends Scala.Functions(JEdit_Resource)
}
