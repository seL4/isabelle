/*  Title:      Pure/PIDE/document_editor.scala
    Author:     Makarius

Central resources and configuration for interactive document preparation.
*/

package isabelle


object Document_Editor {
  /* document output */

  def document_name: String = "document"
  def document_output_dir(): Path = Path.explode("$ISABELLE_HOME_USER/document_output")
  def document_output(name: String): Path = document_output_dir() + Path.basic(name)

  object Meta_Data {
    def read(name: String = document_name): Option[Meta_Data] = {
      val json_path = document_output(name).json
      if (json_path.is_file) {
        val json = JSON.parse(File.read(json_path))
        for {
          selection <- JSON.list(json, "selection", JSON.Value.String.unapply)
          sources <- JSON.string(json, "sources")
          log <- JSON.string(json, "log")
          pdf <- JSON.string(json, "pdf")
        } yield {
          Meta_Data(name,
            selection,
            SHA1.fake_digest(sources),
            SHA1.fake_digest(log),
            SHA1.fake_digest(pdf))
        }
      }
      else None
    }

    def write(
      selection: Set[Document.Node.Name],
      doc: Document_Build.Document_Output,
      name: String = document_name
    ): Unit = {
      val json =
        JSON.Object(
          "selection" -> selection.toList.map(_.theory).sorted,
          "sources" -> doc.sources.toString,
          "log" -> SHA1.digest(doc.log).toString,
          "pdf" -> SHA1.digest(doc.pdf).toString)
      File.write(document_output(name).json, JSON.Format.pretty_print(json))
    }
  }

  sealed case class Meta_Data(
    name: String,
    selection: List[String],
    sources: SHA1.Digest,
    log: SHA1.Digest,
    pdf: SHA1.Digest
  ) {
    def check_files(): Boolean = {
      val path = document_output(name)
      path.log.is_file &&
      path.pdf.is_file &&
      log == SHA1.digest(File.read(path.log)) &&
      pdf == SHA1.digest(path.pdf)
    }
  }

  def write_document(
    selection: Set[Document.Node.Name],
    doc: Document_Build.Document_Output,
    name: String = document_name
  ): Unit = {
    val output = document_output(name)
    File.write(output.log, doc.log)
    Bytes.write(output.pdf, doc.pdf)
    Meta_Data.write(selection, doc, name = name)
  }

  def view_document(name: String = document_name): Unit = {
    val path = document_output(name).pdf
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
