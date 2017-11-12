/*  Title:      Pure/Thy/thy_resources.scala
    Author:     Makarius

PIDE resources for theory files.
*/

package isabelle


object Thy_Resources
{
  /* internal state */

  sealed case class State(theories: Map[Document.Node.Name, Theory] = Map.empty)

  final class Theory private[Thy_Resources](
    val node_name: Document.Node.Name,
    val node_header: Document.Node.Header,
    val text: String)
  {
    override def toString: String = node_name.toString

    def node_perspective: Document.Node.Perspective_Text =
      Document.Node.Perspective(true, Text.Perspective.full, Document.Node.Overlays.empty)

    def node_edits(old: Option[Theory]): List[Document.Edit_Text] =
    {
      val text_edits =
        if (old.isEmpty) Text.Edit.inserts(0, text)
        else Text.Edit.replace(0, old.get.text, text)

      if (text_edits.isEmpty) Nil
      else
        List(node_name -> Document.Node.Deps(node_header),
          node_name -> Document.Node.Edits(text_edits),
          node_name -> node_perspective)
    }
  }
}

class Thy_Resources(session_base: Sessions.Base, log: Logger = No_Logger)
  extends Resources(session_base, log = log)
{
  resources =>

  private val state = Synchronized(Thy_Resources.State())

  def read_thy(node_name: Document.Node.Name): Thy_Resources.Theory =
  {
    val path = node_name.path
    if (!node_name.is_theory) error("Not a theory file: " + path)

    val text = File.read(path)
    val node_header = resources.check_thy_reader(node_name, Scan.char_reader(text))
    new Thy_Resources.Theory(node_name, node_header, text)
  }

  def load_theories(
    session: Session,
    theories: List[(String, Position.T)],
    qualifier: String = Sessions.DRAFT,
    master_dir: String = ""): List[Document.Node.Name] =
  {
    val import_names =
      for ((thy, pos) <- theories)
      yield (import_name(qualifier, master_dir, thy), pos)

    val dependencies = resources.dependencies(import_names).check_errors
    val loaded_theories = dependencies.names.map(read_thy(_))

    val edits =
      state.change_result(st =>
      {
        val theory_edits =
          for {
            theory <- loaded_theories
            node_name = theory.node_name
            edits = theory.node_edits(st.theories.get(node_name))
            if edits.nonEmpty
          } yield ((node_name, theory), edits)

        val st1 = st.copy(theories = st.theories ++ theory_edits.map(_._1))
        (theory_edits.flatMap(_._2), st1)
      })
    session.update(Document.Blobs.empty, edits)

    dependencies.names
  }
}
