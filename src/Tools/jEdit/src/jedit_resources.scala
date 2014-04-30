/*  Title:      Tools/jEdit/src/jedit_resources.scala
    Author:     Makarius

Resources for theories and auxiliary files, based on jEdit buffer
content and virtual file-systems.
*/

package isabelle.jedit


import isabelle._

import java.io.{File => JFile, ByteArrayOutputStream}
import javax.swing.text.Segment

import org.gjt.sp.jedit.io.{VFS, FileVFS, VFSManager}
import org.gjt.sp.jedit.MiscUtilities
import org.gjt.sp.jedit.{jEdit, View, Buffer}
import org.gjt.sp.jedit.bufferio.BufferIORequest


class JEdit_Resources(
    loaded_theories: Set[String],
    known_theories: Map[String, Document.Node.Name],
    base_syntax: Outer_Syntax)
  extends Resources(loaded_theories, known_theories, base_syntax)
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
    else if (path.is_current) dir
    else {
      val vfs = VFSManager.getVFSForPath(dir)
      if (vfs.isInstanceOf[FileVFS])
        MiscUtilities.resolveSymlinks(
          vfs.constructPath(dir, Isabelle_System.platform_path(path)))
      else vfs.constructPath(dir, Isabelle_System.standard_path(path))
    }
  }

  override def with_thy_text[A](name: Document.Node.Name, consume: CharSequence => A): A =
  {
    Swing_Thread.now {
      JEdit_Lib.jedit_buffer(name) match {
        case Some(buffer) =>
          JEdit_Lib.buffer_lock(buffer) {
            Some(consume(buffer.getSegment(0, buffer.getLength)))
          }
        case None => None
      }
    } getOrElse {
      if (Url.is_wellformed(name.node)) consume(Url.read(name.node))
      else {
        val file = new JFile(name.node)
        if (file.isFile) consume(File.read(file))
        else error("No such file: " + quote(file.toString))
      }
    }
  }

  def check_file(view: View, file: String): Boolean =
    try {
      if (Url.is_wellformed(file)) Url.is_readable(file)
      else (new JFile(file)).isFile
    }
    catch { case ERROR(_) => false }


  /* file content */

  private class File_Content_Output(buffer: Buffer) extends
    ByteArrayOutputStream(buffer.getLength + 1)
  {
    def content(): Bytes = Bytes(this.buf, 0, this.count)
  }

  private class File_Content(buffer: Buffer) extends
    BufferIORequest(null, buffer, null, VFSManager.getVFSForPath(buffer.getPath), buffer.getPath)
  {
    def _run() { }
    def content(): Bytes =
    {
      val out = new File_Content_Output(buffer)
      write(buffer, out)
      out.content()
    }
  }

  def file_content(buffer: Buffer): Bytes = (new File_Content(buffer)).content()


  /* theory text edits */

  override def commit(change: Session.Change)
  {
    if (change.syntax_changed) Swing_Thread.later { jEdit.propertiesChanged() }
  }
}

