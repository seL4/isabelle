/*  Title:      Pure/Thy/file_format.scala
    Author:     Makarius

Support for user-defined file formats.
*/

package isabelle


object File_Format
{
  sealed case class Theory_Context(name: Document.Node.Name, content: String)


  /* environment */

  def environment(): Environment =
    new Environment(Isabelle_System.init_classes[File_Format]("ISABELLE_FILE_FORMATS"))

  final class Environment private [File_Format](file_formats: List[File_Format])
  {
    override def toString: String = file_formats.mkString("File_Format.Environment(", ",", ")")

    def get(name: String): Option[File_Format] = file_formats.find(_.detect(name))
    def get(name: Document.Node.Name): Option[File_Format] = get(name.node)
    def get_theory(name: Document.Node.Name): Option[File_Format] = get(name.theory)
    def is_theory(name: Document.Node.Name): Boolean = get_theory(name).isDefined

    def start_session(session: isabelle.Session): Session =
      new Session(file_formats.map(_.start(session)))
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

  object Agent extends Agent
  {
    override def toString: String = "-"
  }
}

trait File_Format
{
  def format_name: String
  override def toString = format_name

  def file_ext: String
  def detect(name: String): Boolean = name.endsWith("." + file_ext)


  /* implicit theory context: name and content */

  def theory_suffix: String = ""
  def theory_content(name: String): String = ""

  def make_theory_name(resources: Resources, name: Document.Node.Name): Option[Document.Node.Name] =
  {
    for {
      (_, ext_name) <- Thy_Header.split_file_name(name.node)
      if detect(ext_name) && theory_suffix.nonEmpty
    }
    yield {
      val thy_node = resources.append(name.node, Path.explode(theory_suffix))
      Document.Node.Name(thy_node, name.master_dir, ext_name)
    }
  }

  def make_theory_content(resources: Resources, thy_name: Document.Node.Name): Option[String] =
  {
    for {
      (prefix, suffix) <- Thy_Header.split_file_name(thy_name.node) if suffix == theory_suffix
      (_, ext_name) <- Thy_Header.split_file_name(prefix) if detect(ext_name)
      s <- proper_string(theory_content(ext_name))
    } yield s
  }

  def make_preview(snapshot: Document.Snapshot): Option[Present.Preview] = None


  /* PIDE session */

  def start(session: isabelle.Session): File_Format.Agent = File_Format.Agent
}
