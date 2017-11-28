/*  Title:      Tools/jEdit/src/jedit_resources.scala
    Author:     Makarius

Resources for theories and auxiliary files, based on jEdit buffer
content and virtual file-systems.
*/

package isabelle.jedit


import isabelle._

import java.io.{File => JFile, ByteArrayOutputStream}
import javax.swing.text.Segment

import scala.util.parsing.input.Reader

import org.gjt.sp.jedit.io.{VFS, FileVFS, VFSManager}
import org.gjt.sp.jedit.MiscUtilities
import org.gjt.sp.jedit.{jEdit, View, Buffer}
import org.gjt.sp.jedit.bufferio.BufferIORequest


object JEdit_Resources
{
  def apply(options: Options): JEdit_Resources =
    new JEdit_Resources(JEdit_Sessions.session_base_info(options))
}

class JEdit_Resources private(val session_base_info: Sessions.Base_Info)
  extends Resources(session_base_info.base.platform_path)
{
  def session_name: String = session_base_info.session
  def session_errors: List[String] = session_base_info.errors


  /* document node name */

  def known_file(path: String): Option[Document.Node.Name] =
    JEdit_Lib.check_file(path).flatMap(session_base.known.get_file(_, bootstrap = true))

  def node_name(path: String): Document.Node.Name =
    known_file(path) getOrElse {
      val vfs = VFSManager.getVFSForPath(path)
      val node = if (vfs.isInstanceOf[FileVFS]) MiscUtilities.resolveSymlinks(path) else path
      val theory = theory_name(Sessions.DRAFT, Thy_Header.theory_name(node))
      if (session_base.loaded_theory(theory)) Document.Node.Name.loaded_theory(theory)
      else {
        val master_dir = if (theory == "") "" else vfs.getParentOfPath(path)
        Document.Node.Name(node, master_dir, theory)
      }
    }

  def node_name(buffer: Buffer): Document.Node.Name =
    node_name(JEdit_Lib.buffer_name(buffer))

  def theory_node_name(buffer: Buffer): Option[Document.Node.Name] =
  {
    val name = node_name(buffer)
    if (name.is_theory) Some(name) else None
  }

  override def append(dir: String, source_path: Path): String =
  {
    val path = source_path.expand
    if (dir == "" || path.is_absolute)
      MiscUtilities.resolveSymlinks(File.platform_path(path))
    else if (path.is_current) dir
    else {
      val vfs = VFSManager.getVFSForPath(dir)
      if (vfs.isInstanceOf[FileVFS])
        MiscUtilities.resolveSymlinks(
          vfs.constructPath(dir, File.platform_path(path)))
      else vfs.constructPath(dir, File.standard_path(path))
    }
  }


  /* file content */

  def read_file_content(node_name: Document.Node.Name): Option[String] =
  {
    val name = node_name.node
    try {
      val text =
        if (Url.is_wellformed(name)) Url.read(Url(name))
        else File.read(new JFile(name))
      Some(Symbol.decode(Line.normalize(text)))
    }
    catch { case ERROR(_) => None }
  }

  def get_file_content(node_name: Document.Node.Name): Option[String] =
    Document_Model.get(node_name) match {
      case Some(model: Buffer_Model) => Some(JEdit_Lib.buffer_text(model.buffer))
      case Some(model: File_Model) => Some(model.content.text)
      case None => read_file_content(node_name)
    }

  override def with_thy_reader[A](name: Document.Node.Name, f: Reader[Char] => A): A =
  {
    GUI_Thread.now {
      Document_Model.get(name) match {
        case Some(model: Buffer_Model) =>
          JEdit_Lib.buffer_lock(model.buffer) { Some(f(JEdit_Lib.buffer_reader(model.buffer))) }
        case Some(model: File_Model) => Some(f(Scan.char_reader(model.content.text)))
        case None => None
      }
    } getOrElse {
      if (Url.is_wellformed(name.node)) f(Scan.byte_reader(Url(name.node)))
      else {
        val file = new JFile(name.node)
        if (file.isFile) f(Scan.byte_reader(file))
        else error("No such file: " + quote(file.toString))
      }
    }
  }


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

  def make_file_content(buffer: Buffer): Bytes = (new File_Content(buffer)).content()


  /* theory text edits */

  override def commit(change: Session.Change)
  {
    if (change.syntax_changed.nonEmpty)
      GUI_Thread.later { Document_Model.syntax_changed(change.syntax_changed) }
    if (change.deps_changed ||
        PIDE.options.bool("jedit_auto_resolve") && undefined_blobs(change.version.nodes).nonEmpty)
      PIDE.plugin.deps_changed()
  }
}
