/*  Title:      Tools/jEdit/src/isabelle_vfs.scala
    Author:     Makarius

Support for virtual file-systems.
*/

package isabelle.jedit


import isabelle._

import java.awt.Component

import org.gjt.sp.jedit.io.{VFS, VFSManager, VFSFile}


class Isabelle_VFS(prefix: String,
  read: Boolean = false,
  write: Boolean = false,
  browse: Boolean = false,
  delete: Boolean = false,
  rename: Boolean = false,
  mkdir: Boolean = false,
  low_latency: Boolean = false,
  case_insensitive: Boolean = false,
  non_awt_session: Boolean = false)
  extends VFS(Library.perhaps_unsuffix(":", prefix),
    (if (read) VFS.READ_CAP else 0) |
    (if (write) VFS.WRITE_CAP else 0) |
    (if (browse) VFS.BROWSE_CAP else 0) |
    (if (delete) VFS.DELETE_CAP else 0) |
    (if (rename) VFS.RENAME_CAP else 0) |
    (if (mkdir) VFS.MKDIR_CAP else 0) |
    (if (low_latency) VFS.LOW_LATENCY_CAP else 0) |
    (if (case_insensitive) VFS.CASE_INSENSITIVE_CAP else 0) |
    (if (non_awt_session) VFS.NON_AWT_SESSION_CAP else 0))
{
  /* URL structure */

  def explode_name(s: String): List[String] = space_explode(getFileSeparator, s)
  def implode_name(elems: Iterable[String]): String = elems.mkString(getFileSeparator.toString)

  def explode_url(url: String, component: Component = null): Option[List[String]] =
  {
    Library.try_unprefix(prefix, url) match {
      case Some(path) => Some(explode_name(path).filter(_.nonEmpty))
      case None =>
        if (component != null) VFSManager.error(component, url, "ioerror.badurl", Array(url))
        None
    }
  }
  def implode_url(elems: Iterable[String]): String = prefix + implode_name(elems)

  override def constructPath(parent: String, path: String): String =
  {
    if (parent == "") path
    else if (parent(parent.length - 1) == getFileSeparator || parent == prefix) parent + path
    else parent + getFileSeparator + path
  }


  /* directory content */

  override def isMarkersFileSupported: Boolean = false

  def make_entry(path: String, is_dir: Boolean = false, size: Long = 0L): VFSFile =
  {
    val entry = explode_name(path).lastOption getOrElse ""
    val url = prefix + path
    new VFSFile(entry, url, url, if (is_dir) VFSFile.DIRECTORY else VFSFile.FILE, size, false)
  }

  override def _getFile(vfs_session: AnyRef, url: String, component: Component): VFSFile =
  {
    val parent = getParentOfPath(url)
    if (parent == prefix) null
    else {
      val files = _listFiles(vfs_session, parent, component)
      if (files == null) null
      else files.find(_.getPath == url) getOrElse null
    }
  }
}
