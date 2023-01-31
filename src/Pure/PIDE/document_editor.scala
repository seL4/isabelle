/*  Title:      Pure/PIDE/document_editor.scala
    Author:     Makarius

Central resources and configuration for interactive document preparation.
*/

package isabelle


object Document_Editor {
  /* document output */

  def document_name: String = "document"
  def document_output_dir(): Path = Path.explode("$ISABELLE_HOME_USER/document_output")
  def document_output(): Path = document_output_dir() + Path.basic(document_name)

  def view_document(): Unit = {
    val path = document_output().pdf
    if (path.is_file) Isabelle_System.pdf_viewer(path)
  }


  /* configuration state */

  sealed case class Session(
    background: Option[Sessions.Background],
    selection: Set[Document.Node.Name],
    snapshot: Option[Document.Snapshot]
  ) {
    def is_vacuous: Boolean = background.isEmpty
    def is_pending: Boolean = snapshot.isEmpty
    def is_ready: Boolean = background.isDefined && snapshot.isDefined

    def get_background: Sessions.Background = background.get
    def get_variant: Document_Build.Document_Variant = get_background.info.documents.head
    def get_snapshot: Document.Snapshot = snapshot.get
  }

  sealed case class State(
    session_background: Option[Sessions.Background] = None,
    selection: Set[Document.Node.Name] = Set.empty,
    views: Set[AnyRef] = Set.empty,
  ) {
    def is_active: Boolean = session_background.isDefined && views.nonEmpty

    def all_document_theories: List[Document.Node.Name] =
      session_background match {
        case Some(background) => background.base.all_document_theories
        case None => Nil
      }

    def active_document_theories: List[Document.Node.Name] =
      if (is_active) all_document_theories else Nil

    def select(
      names: Iterable[Document.Node.Name],
      set: Boolean = false,
      toggle: Boolean = false
    ): State = {
      copy(selection =
        names.foldLeft(selection) {
          case (sel, name) =>
            val b = if (toggle) !selection(name) else set
            if (b) sel + name else sel - name
        })
    }

    def register_view(id: AnyRef): State = copy(views = views + id)
    def unregister_view(id: AnyRef): State = copy(views = views - id)

    def session(pide_session: isabelle.Session): Session = {
      val background = session_background.filter(_.info.documents.nonEmpty)
      val snapshot =
        if (background.isEmpty) None
        else {
          val snapshot = pide_session.snapshot()
          def document_ready(name: Document.Node.Name): Boolean =
            pide_session.resources.session_base.loaded_theory(name) ||
            snapshot.node_consolidated(name)
          if (snapshot.is_outdated || !selection.forall(document_ready)) None
          else Some(snapshot)
        }
      Session(background, selection, snapshot)
    }
  }
}
