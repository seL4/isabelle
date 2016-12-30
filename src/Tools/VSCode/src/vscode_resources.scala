/*  Title:      Tools/VSCode/src/vscode_resources.scala
    Author:     Makarius

Resources for VSCode Language Server, based on file-system URIs.
*/

package isabelle.vscode


import isabelle._

import java.net.{URI, URISyntaxException}
import java.io.{File => JFile}


object VSCode_Resources
{
  /* file URIs */

  def is_wellformed(uri: String): Boolean =
    try { new JFile(new URI(uri)); true }
    catch { case _: URISyntaxException | _: IllegalArgumentException => false }

  def canonical_file(uri: String): JFile =
    new JFile(new URI(uri)).getCanonicalFile


  /* internal state */

  sealed case class State(
    models: Map[String, Document_Model] = Map.empty,
    pending_input: Set[String] = Set.empty,
    pending_output: Set[String] = Set.empty)
}

class VSCode_Resources(
    val options: Options,
    val text_length: Text.Length,
    loaded_theories: Set[String],
    known_theories: Map[String, Document.Node.Name],
    base_syntax: Outer_Syntax)
  extends Resources(loaded_theories, known_theories, base_syntax)
{
  private val state = Synchronized(VSCode_Resources.State())


  /* document node name */

  def node_name(uri: String): Document.Node.Name =
  {
    val theory = Thy_Header.thy_name(uri).getOrElse("")
    val master_dir =
      if (!VSCode_Resources.is_wellformed(uri) || theory == "") ""
      else VSCode_Resources.canonical_file(uri).getParent
    Document.Node.Name(uri, master_dir, theory)
  }


  /* document models */

  def get_model(uri: String): Option[Document_Model] = state.value.models.get(uri)

  def update_model(session: Session, uri: String, text: String)
  {
    state.change(st =>
      {
        val model = st.models.getOrElse(uri, Document_Model.init(session, uri))
        val model1 = (model.update_text(text) getOrElse model).copy(external = false)
        st.copy(
          models = st.models + (uri -> model1),
          pending_input = st.pending_input + uri)
      })
  }

  def close_model(uri: String): Option[Document_Model] =
    state.change_result(st =>
      st.models.get(uri) match {
        case None => (None, st)
        case Some(model) =>
          (Some(model), st.copy(models = st.models + (uri -> model.copy(external = true))))
      })

  def sync_external(changed_files: Set[JFile]): Boolean =
    state.change_result(st =>
      {
        val changed =
          (for {
            (uri, model) <- st.models.iterator
            if changed_files(model.file)
            model1 <- model.update_file
          } yield (uri, model)).toList
        if (changed.isEmpty) (false, st)
        else (true, st.copy(models = (st.models /: changed)(_ + _)))
      })


  /* pending input */

  def flush_input(session: Session)
  {
    state.change(st =>
      {
        val changed =
          (for {
            uri <- st.pending_input.iterator
            model <- st.models.get(uri)
            res <- model.flush_edits
          } yield res).toList

        session.update(Document.Blobs.empty, changed.flatMap(_._1))
        st.copy(
          models = (st.models /: changed) { case (ms, (_, m)) => ms + (m.uri -> m) },
          pending_input = Set.empty)
      })
  }


  /* pending output */

  def update_output(changed_nodes: List[String]): Unit =
    state.change(st => st.copy(pending_output = st.pending_output ++ changed_nodes))

  def flush_output(channel: Channel)
  {
    state.change(st =>
      {
        val changed_iterator =
          for {
            uri <- st.pending_output.iterator
            model <- st.models.get(uri)
            rendering = model.rendering()
            (diagnostics, model1) <- model.publish_diagnostics(rendering)
          } yield {
            channel.diagnostics(model1.uri, rendering.diagnostics_output(diagnostics))
            model1
          }
        st.copy(
          models = (st.models /: changed_iterator) { case (ms, m) => ms + (m.uri -> m) },
          pending_output = Set.empty)
      }
    )
  }
}
