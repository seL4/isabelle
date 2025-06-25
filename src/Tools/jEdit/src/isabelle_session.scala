/*  Title:      Tools/jEdit/src/isabelle_session.scala
    Author:     Makarius

Access Isabelle session information via virtual file-system.
*/

package isabelle.jedit


import isabelle._

import java.awt.Component

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.io.{VFS => JEdit_VFS, VFSFile}
import org.gjt.sp.jedit.browser.VFSBrowser


object Isabelle_Session {
  /* virtual file-system */

  val vfs_prefix = "isabelle-session:"

  class Session_Entry(name: String, path: String, marker: String)
  extends VFSFile(name, path, vfs_prefix + name, VFSFile.FILE, 0L, false) {
    override def getPathMarker: String = marker

    override def getExtendedAttribute(att: String): String =
      if (att == JEdit_VFS.EA_SIZE) null
      else super.getExtendedAttribute(att)
  }

  class VFS
  extends Isabelle_VFS(
    vfs_prefix,
    read = true,
    browse = true,
    low_latency = true,
    non_awt_session = true
  ) {
    override def _listFiles(
      vfs_session: AnyRef,
      url: String,
      component: Component
    ): Array[VFSFile] = {
      explode_url(url, component = component) match {
        case None => null
        case Some(elems) =>
          val sessions = JEdit_Session.sessions_structure()
          elems match {
            case Nil =>
              sessions.relevant_chapters.sortBy(_.name).map(ch => make_entry(ch.name, is_dir = true)).toArray
            case List(chapter) =>
              sessions.relevant_chapters.find(_.name == chapter) match {
                case None => null
                case Some(ch) =>
                  ch.sessions.map { session =>
                    val pos = sessions(session).pos
                    val name = ch.name + "/" + session
                    val path =
                      Position.File.unapply(pos) match {
                        case Some(path) => File.platform_path(path)
                        case None => null
                      }
                    val marker =
                      Position.Line.unapply(pos) match {
                        case Some(line) => "+line:" + line
                        case None => null
                      }
                    new Session_Entry(name, path, marker)
                  }.toArray
              }
            case _ => null
          }
      }
    }
  }


  /* open browser */

  def open_browser(view: View): Unit = {
    val path =
      PIDE.maybe_snapshot(view) match {
        case None => ""
        case Some(snapshot) =>
          val sessions_structure = JEdit_Session.sessions_structure()
          val session = sessions_structure.theory_qualifier(snapshot.node_name)
          val chapter =
            sessions_structure.get(session) match {
              case Some(info) => info.chapter
              case None => Sessions.UNSORTED
            }
          chapter
      }
    VFSBrowser.browseDirectory(view, vfs_prefix + path)
  }
}
