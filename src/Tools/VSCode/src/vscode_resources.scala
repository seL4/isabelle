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
    pending_input: Set[Document.Node.Name] = Set.empty,
    pending_output: Set[Document.Node.Name] = Set.empty)
}

class VSCode_Resources(
    val options: Options,
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

  def update_model(model: Document_Model)
  {
    state.change(st =>
      st.copy(
        models = st.models + (model.node_name.node -> model),
        pending_input = st.pending_input + model.node_name))
  }


  /* pending input */

  def flush_input(session: Session)
  {
    state.change(st =>
      {
        val changed =
          (for {
            node_name <- st.pending_input.iterator
            model <- st.models.get(node_name.node)
            if model.changed } yield model).toList
        val edits = for { model <- changed; edit <- model.node_edits } yield edit
        session.update(Document.Blobs.empty, edits)
        st.copy(
          models = (st.models /: changed) { case (ms, m) => ms + (m.uri -> m.unchanged) },
          pending_input = Set.empty)
      })
  }


  /* pending output */

  def update_output(changed_nodes: Set[Document.Node.Name]): Unit =
    state.change(st => st.copy(pending_output = st.pending_output ++ changed_nodes))

  def flush_output(channel: Channel)
  {
    state.change(st =>
      {
        val changed_iterator =
          for {
            node_name <- st.pending_output.iterator
            model <- st.models.get(node_name.node)
            rendering = model.rendering(options)
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
