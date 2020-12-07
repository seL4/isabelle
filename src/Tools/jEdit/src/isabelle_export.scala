/*  Title:      Tools/jEdit/src/isabelle_export.scala
    Author:     Makarius

Access Isabelle theory exports via virtual file-system.
*/

package isabelle.jedit


import isabelle._

import java.awt.Component
import java.io.InputStream

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.io.VFSFile
import org.gjt.sp.jedit.browser.VFSBrowser


object Isabelle_Export
{
  /* virtual file-system */

  val vfs_prefix = "isabelle-export:"

  class VFS extends Isabelle_VFS(vfs_prefix,
    read = true, browse = true, low_latency = true, non_awt_session = true)
  {
    override def _listFiles(vfs_session: AnyRef, url: String, component: Component): Array[VFSFile] =
    {
      explode_url(url, component = component) match {
        case None => null
        case Some(elems) =>
          val snapshot = PIDE.session.await_stable_snapshot()
          val version = snapshot.version
          elems match {
            case Nil =>
              (for {
                (node_name, _) <- version.nodes.iterator
                if !snapshot.state.node_exports(version, node_name).is_empty
              } yield make_entry(node_name.theory, is_dir = true)).toArray
            case theory :: prefix =>
              val depth = prefix.length + 1
              val entries: List[(String, Option[Long])] =
                (for {
                  (node_name, _) <- version.nodes.iterator if node_name.theory == theory
                  exports = snapshot.state.node_exports(version, node_name)
                  (_, entry) <- exports.iterator if entry.name_extends(prefix)
                } yield {
                  val is_dir = entry.name_elems.length > depth
                  val path = Export.implode_name(theory :: entry.name_elems.take(depth))
                  val file_size = if (is_dir) None else Some(entry.uncompressed.length.toLong)
                  (path, file_size)
                }).toSet.toList
              (for ((path, file_size) <- entries.iterator) yield {
                file_size match {
                  case None => make_entry(path, is_dir = true)
                  case Some(size) => make_entry(path, size = size)
                }
              }).toArray
          }
      }
    }

    override def _createInputStream(
      vfs_session: AnyRef, url: String, ignore_errors: Boolean, component: Component): InputStream =
    {
      explode_url(url, component = if (ignore_errors) null else component) match {
        case None | Some(Nil) => Bytes.empty.stream()
        case Some(theory :: name_elems) =>
          val snapshot = PIDE.session.await_stable_snapshot()
          val version = snapshot.version
          val bytes =
            (for {
              (node_name, _) <- version.nodes.iterator
              if node_name.theory == theory
              (_, entry) <- snapshot.state.node_exports(version, node_name).iterator
              if entry.name_elems == name_elems
            } yield entry.uncompressed).find(_ => true).getOrElse(Bytes.empty)

          bytes.stream()
      }
    }
  }


  /* open browser */

  def open_browser(view: View)
  {
    val path =
      PIDE.maybe_snapshot(view) match {
        case None => ""
        case Some(snapshot) => snapshot.node_name.theory
      }
    VFSBrowser.browseDirectory(view, vfs_prefix + path)
  }
}
