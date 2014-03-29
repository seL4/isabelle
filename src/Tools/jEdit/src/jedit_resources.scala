/*  Title:      Tools/jEdit/src/jedit_resources.scala
    Author:     Makarius

Resources for theories and auxiliary files, based on jEdit buffer
content and virtual file-systems.
*/

package isabelle.jedit


import isabelle._

import java.io.{File => JFile, IOException, ByteArrayOutputStream}
import javax.swing.text.Segment

import org.gjt.sp.jedit.io.{VFS, FileVFS, VFSFile, VFSManager}
import org.gjt.sp.jedit.MiscUtilities
import org.gjt.sp.jedit.{jEdit, View, Buffer}
import org.gjt.sp.jedit.bufferio.BufferIORequest


class JEdit_Resources(loaded_theories: Set[String] = Set.empty, base_syntax: Outer_Syntax)
  extends Resources(loaded_theories, base_syntax)
{
  /* document node names */

  def node_name(buffer: Buffer): Document.Node.Name =
  {
    val node = JEdit_Lib.buffer_name(buffer)
    val theory = Thy_Header.thy_name(node).getOrElse("")
    val master_dir = if (theory == "") "" else buffer.getDirectory
    Document.Node.Name(node, master_dir, theory)
  }

  def theory_node_name(buffer: Buffer): Option[Document.Node.Name] =
  {
    val name = node_name(buffer)
    if (name.is_theory) Some(name) else None
  }


  /* file-system operations */

  override def append(dir: String, source_path: Path): String =
  {
    val path = source_path.expand
    if (dir == "" || path.is_absolute) Isabelle_System.platform_path(path)
    else {
      val vfs = VFSManager.getVFSForPath(dir)
      if (vfs.isInstanceOf[FileVFS])
        MiscUtilities.resolveSymlinks(
          vfs.constructPath(dir, Isabelle_System.platform_path(path)))
      else vfs.constructPath(dir, Isabelle_System.standard_path(path))
    }
  }

  override def with_thy_text[A](name: Document.Node.Name, f: CharSequence => A): A =
  {
    Swing_Thread.now {
      JEdit_Lib.jedit_buffer(name.node) match {
        case Some(buffer) =>
          JEdit_Lib.buffer_lock(buffer) {
            Some(f(buffer.getSegment(0, buffer.getLength)))
          }
        case None => None
      }
    } getOrElse {
      val file = new JFile(name.node)  // FIXME load URL via jEdit VFS (!?)
      if (!file.exists || !file.isFile) error("No such file: " + quote(file.toString))
      f(File.read(file))
    }
  }

  def check_file(view: View, path: String): Boolean =
  {
    val vfs = VFSManager.getVFSForPath(path)
    val session = vfs.createVFSSession(path, view)

    try {
      session != null && {
        try {
          val file = vfs._getFile(session, path, view)
          file != null && file.isReadable && file.getType == VFSFile.FILE
        }
        catch { case _: IOException => false }
      }
    }
    finally {
      try { vfs._endVFSSession(session, view) }
      catch { case _: IOException => }
    }
  }


  /* file content */

  def file_content(buffer: Buffer): Bytes =
  {
    val path = buffer.getPath
    val vfs = VFSManager.getVFSForPath(path)
    val content =
      new BufferIORequest(null, buffer, null, vfs, path) {
        def _run() { }
        def apply(): Bytes =
        {
          val out =
            new ByteArrayOutputStream(buffer.getLength + 1) {
              def content(): Bytes = Bytes(this.buf, 0, this.count)
            }
          write(buffer, out)
          out.content()
        }
      }
    content()
  }


  /* theory text edits */

  override def commit(change: Session.Change)
  {
    if (change.syntax_changed) Swing_Thread.later { jEdit.propertiesChanged() }
    if (change.deps_changed) PIDE.deps_changed()
  }
}

