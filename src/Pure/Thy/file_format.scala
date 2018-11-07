/*  Title:      Pure/Thy/file_format.scala
    Author:     Makarius

Support for user-defined file formats.
*/

package isabelle


object File_Format
{
  def environment(): Environment =
  {
    val file_formats =
      for (name <- space_explode(':', Isabelle_System.getenv_strict("ISABELLE_CLASSES_FILE_FORMAT")))
      yield {
        def err(msg: String): Nothing =
          error("Bad entry " + quote(name) + " in ISABELLE_CLASSES_FILE_FORMAT\n" + msg)

        try { Class.forName(name).asInstanceOf[Class[File_Format]].newInstance() }
        catch {
          case _: ClassNotFoundException => err("Class not found")
          case exn: Throwable => err(Exn.message(exn))
        }
      }
    new Environment(file_formats)
  }

  final class Environment private [File_Format](file_formats: List[File_Format])
  {
    override def toString: String = file_formats.mkString("File_Format.Environment(", ",", ")")

    def get(name: String): Option[File_Format] = file_formats.find(_.detect(name))
    def get(name: Document.Node.Name): Option[File_Format] = get(name.node)
    def get_theory(name: Document.Node.Name): Option[File_Format] = get(name.theory)
    def is_theory(name: Document.Node.Name): Boolean = get_theory(name).isDefined
  }

  sealed case class Theory_Context(name: Document.Node.Name, content: String)
}

trait File_Format
{
  def format_name: String
  override def toString = format_name

  def detect(name: String): Boolean

  def make_theory_name(
    resources: Resources, name: Document.Node.Name): Option[Document.Node.Name] = None

  def make_theory_content(
    resources: Resources, thy_name: Document.Node.Name): Option[String] = None

  def make_preview(snapshot: Document.Snapshot): Option[Present.Preview] = None
}
