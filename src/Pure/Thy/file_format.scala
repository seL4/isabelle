/*  Title:      Pure/Thy/file_format.scala
    Author:     Makarius

Support for user-defined file formats.
*/

package isabelle


object File_Format
{
  sealed case class Theory_Context(name: Document.Node.Name, content: String)


  /* registry */

  lazy val registry: Registry =
    new Registry(Isabelle_System.make_services(classOf[File_Format]))

  final class Registry private [File_Format](file_formats: List[File_Format])
  {
    override def toString: String = file_formats.mkString("File_Format.Environment(", ",", ")")

    def get(name: String): Option[File_Format] = file_formats.find(_.detect(name))
    def get(name: Document.Node.Name): Option[File_Format] = get(name.node)
    def get_theory(name: Document.Node.Name): Option[File_Format] = get(name.theory)
    def is_theory(name: Document.Node.Name): Boolean = get_theory(name).isDefined

    def start_session(session: isabelle.Session): Session =
      new Session(file_formats.map(_.start(session)).filterNot(_ == No_Agent))
  }


  /* session */

  final class Session private[File_Format](agents: List[Agent])
  {
    override def toString: String =
      agents.mkString("File_Format.Session(", ", ", ")")

    def prover_options(options: Options): Options =
      (options /: agents)({ case (opts, agent) => agent.prover_options(opts) })

    def stop_session { agents.foreach(_.stop) }
  }

  trait Agent
  {
    def prover_options(options: Options): Options = options
    def stop {}
  }

  object No_Agent extends Agent
}

abstract class File_Format extends Isabelle_System.Service
{
  def format_name: String
  override def toString: String = "File_Format(" + format_name + ")"

  def file_ext: String
  def detect(name: String): Boolean = name.endsWith("." + file_ext)


  /* implicit theory context: name and content */

  def theory_suffix: String = ""
  def theory_content(name: String): String = ""

  def make_theory_name(resources: Resources, name: Document.Node.Name): Option[Document.Node.Name] =
  {
    for {
      (_, thy) <- Thy_Header.split_file_name(name.node)
      if detect(name.node) && theory_suffix.nonEmpty
    }
    yield {
      val thy_node = resources.append(name.node, Path.explode(theory_suffix))
      Document.Node.Name(thy_node, name.master_dir, thy)
    }
  }

  def make_theory_content(resources: Resources, thy_name: Document.Node.Name): Option[String] =
  {
    for {
      (prefix, suffix) <- Thy_Header.split_file_name(thy_name.node)
      if detect(prefix) && suffix == theory_suffix
      (_, thy) <- Thy_Header.split_file_name(prefix)
      s <- proper_string(theory_content(thy))
    } yield s
  }

  def make_preview(snapshot: Document.Snapshot): Option[Presentation.Preview] = None


  /* PIDE session agent */

  def start(session: isabelle.Session): File_Format.Agent = File_Format.No_Agent
}
