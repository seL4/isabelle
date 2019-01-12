/*  Title:      Tools/jEdit/src/isabelle_export.scala
    Author:     Makarius

Access Isabelle theory exports via virtual file-system.
*/

package isabelle.jedit


import isabelle._

import java.awt.Component
import java.io.InputStream

import org.gjt.sp.jedit.{Buffer, View}
import org.gjt.sp.jedit.io.{VFS => JEditVFS, VFSFile, VFSManager}
import org.gjt.sp.jedit.bufferio.BufferLoadRequest


object Isabelle_Export
{
  val vfs_name = "isabelle-export"
  val vfs_caps =
    JEditVFS.READ_CAP |
    JEditVFS.BROWSE_CAP |
    JEditVFS.LOW_LATENCY_CAP |
    JEditVFS.NON_AWT_SESSION_CAP

  val vfs_prefix = vfs_name + ":"

  def vfs_error(component: Component, path: String, prop: String, args: AnyRef*): Unit =
    VFSManager.error(component, path, prop, args.toArray)

  def vfs_file(path: String, is_dir: Boolean = false, size: Long = 0L): VFSFile =
  {
    val name = Export.explode_name(path).lastOption getOrElse ""
    val url = vfs_prefix + path
    new VFSFile(name, url, url, if (is_dir) VFSFile.DIRECTORY else VFSFile.FILE, size, false)
  }

  def explode_url(url: String, component: Component = null): Option[List[String]] =
  {
    Library.try_unprefix(vfs_prefix, url) match {
      case Some(path) => Some(Export.explode_name(path).filter(_.nonEmpty))
      case None =>
        if (component != null) vfs_error(component, url, "ioerror.badurl", url)
        None
    }
  }

  class VFS extends JEditVFS(vfs_name, vfs_caps)
  {
    override def constructPath(parent: String, path: String): String =
    {
      if (parent == vfs_prefix || parent.endsWith(Export.sep)) parent + path
      else parent + Export.sep + path
    }

    override def _listFiles(session: AnyRef, url: String, component: Component): Array[VFSFile] =
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
              } yield vfs_file(node_name.theory, is_dir = true)).toArray
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
                  val file_size = if (is_dir) None else Some(entry.uncompressed().length.toLong)
                  (path, file_size)
                }).toSet.toList
              (for ((path, file_size) <- entries.iterator) yield {
                file_size match {
                  case None => vfs_file(path, is_dir = true)
                  case Some(size) => vfs_file(path, size = size)
                }
              }).toArray
          }
      }
    }

    override def _getFile(session: AnyRef, url: String, component: Component): VFSFile =
    {
      val parent = getParentOfPath(url)
      if (parent == vfs_prefix) null
      else {
        val files = _listFiles(session, parent, component)
        if (files == null) null
        else files.find(_.getPath == url) getOrElse null
      }
    }

    override def _createInputStream(
      session: AnyRef, url: String, ignore_errors: Boolean, component: Component): InputStream =
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
            } yield entry.uncompressed()).find(_ => true).getOrElse(Bytes.empty)

          bytes.stream()
      }
    }
  }
}
