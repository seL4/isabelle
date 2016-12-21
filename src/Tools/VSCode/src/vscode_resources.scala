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
  def is_wellformed(uri: String): Boolean =
    try { new JFile(new URI(uri)); true }
    catch { case _: URISyntaxException | _: IllegalArgumentException => false }

  def canonical_file(uri: String): JFile =
    new JFile(new URI(uri)).getCanonicalFile

  val empty: VSCode_Resources =
    new VSCode_Resources(Set.empty, Map.empty, Outer_Syntax.empty)
}

class VSCode_Resources(
    loaded_theories: Set[String],
    known_theories: Map[String, Document.Node.Name],
    base_syntax: Outer_Syntax)
  extends Resources(loaded_theories, known_theories, base_syntax)
{
  def node_name(uri: String): Document.Node.Name =
  {
    val theory = Thy_Header.thy_name(uri).getOrElse("")
    val master_dir =
      if (!VSCode_Resources.is_wellformed(uri) || theory == "") ""
      else VSCode_Resources.canonical_file(uri).getParent
    Document.Node.Name(uri, master_dir, theory)
  }
}
