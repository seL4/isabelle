/*  Title:      Pure/Thy/thy_resources.scala
    Author:     Makarius

PIDE resources for theory files.
*/

package isabelle


object Thy_Resources
{
  /* internal state */

  sealed case class State(
    models: Map[Document.Node.Name, Thy_Document_Model] = Map.empty)
  {
    def update_models(changed: List[Thy_Document_Model]): State =
      copy(models = models ++ changed.iterator.map(model => (model.node_name, model)))
  }
}

class Thy_Resources(session_base: Sessions.Base, log: Logger = No_Logger)
  extends Resources(session_base, log = log)
{
  resources =>

  private val state = Synchronized(Thy_Resources.State())

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
    val loaded_models = dependencies.names.map(Thy_Document_Model.read_file(session, _))

    val edits =
      state.change_result(st =>
      {
        val model_edits =
          for {
            model <- loaded_models
            edits = model.node_edits(st.models.get(model.node_name))
            if edits.nonEmpty
          } yield model -> edits

        val st1 = st.update_models(model_edits.map(_._1))
        (model_edits.flatMap(_._2), st1)
      })
    session.update(Document.Blobs.empty, edits)

    dependencies.names
  }
}
