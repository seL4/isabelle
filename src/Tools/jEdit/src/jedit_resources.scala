/*  Title:      Tools/jEdit/src/jedit_resources.scala
    Author:     Makarius

Resources for theories and auxiliary files, based on jEdit buffer
content and virtual file-systems.
*/

package isabelle.jedit


import isabelle._

import java.io.{File => JFile, ByteArrayOutputStream}

import scala.util.parsing.input.Reader

import org.gjt.sp.jedit.io.{FileVFS, VFSManager}
import org.gjt.sp.jedit.MiscUtilities
import org.gjt.sp.jedit.Buffer
import org.gjt.sp.jedit.bufferio.BufferIORequest


object JEdit_Resources {
  def apply(options: Options): JEdit_Resources =
    new JEdit_Resources(JEdit_Session.session_background(options))
}

class JEdit_Resources private(session_background: Sessions.Background)
extends Resources(session_background) {
  /* document node name */

  def node_name(path: String): Document.Node.Name =
    JEdit_Lib.check_file(path).flatMap(find_theory) getOrElse {
      val vfs = VFSManager.getVFSForPath(path)
      val node = if (vfs.isInstanceOf[FileVFS]) MiscUtilities.resolveSymlinks(path) else path
      val theory = theory_name(Sessions.DRAFT, Thy_Header.theory_name(node))
      if (session_base.loaded_theory(theory)) Document.Node.Name.loaded_theory(theory)
      else Document.Node.Name(node, theory = theory)
    }

  def node_name(buffer: Buffer): Document.Node.Name =
    node_name(JEdit_Lib.buffer_name(buffer))

  def theory_node_name(buffer: Buffer): Option[Document.Node.Name] = {
    val name = node_name(buffer)
    if (name.is_theory) Some(name) else None
  }

  override def migrate_name(standard_name: Document.Node.Name): Document.Node.Name =
    node_name(File.platform_path(Path.explode(standard_name.node).canonical))

  override def append_path(prefix: String, source_path: Path): String = {
    val path = source_path.expand
    if (prefix == "" || path.is_absolute) {
      MiscUtilities.resolveSymlinks(File.platform_path(path))
    }
    else if (path.is_current) prefix
    else {
      val vfs = VFSManager.getVFSForPath(prefix)
      if (vfs.isInstanceOf[FileVFS]) {
        MiscUtilities.resolveSymlinks(
          vfs.constructPath(prefix, File.platform_path(path)))
      }
      else vfs.constructPath(prefix, File.standard_path(path))
    }
  }

  override def read_dir(dir: String): List[String] = {
    val vfs = VFSManager.getVFSForPath(dir)
    if (vfs.isInstanceOf[FileVFS]) File.read_dir(Path.explode(File.standard_path(dir)))
    else Nil
  }


  /* file content */

  def read_file_content(node_name: Document.Node.Name): Option[String] = {
    make_theory_content(node_name) orElse {
      val name = node_name.node
      try {
        val text =
          if (Url.is_wellformed(name)) Url.read(name)
          else File.read(new JFile(name))
        Some(Symbol.decode(Line.normalize(text)))
      }
      catch { case ERROR(_) => None }
    }
  }

  def get_file_content(node_name: Document.Node.Name): Option[String] =
    Document_Model.get_model(node_name) match {
      case Some(model: Buffer_Model) => Some(JEdit_Lib.buffer_text(model.buffer))
      case Some(model: File_Model) => Some(model.content.text)
      case None => read_file_content(node_name)
    }

  override def with_thy_reader[A](name: Document.Node.Name, f: Reader[Char] => A): A = {
    GUI_Thread.now {
      Document_Model.get_model(name) match {
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


  private class File_Content_Output(buffer: Buffer)
  extends ByteArrayOutputStream(buffer.getLength + 1) {
    def content(): Bytes = Bytes(this.buf, 0, this.count)
  }

  private class File_Content_Request(buffer: Buffer)
  extends BufferIORequest(null, buffer, null, VFSManager.getVFSForPath(buffer.getPath), buffer.getPath) {
    def _run(): Unit = {}
    def content(): Bytes = {
      val out = new File_Content_Output(buffer)
      write(buffer, out)
      out.content()
    }
  }

  def make_file_content(buffer: Buffer): Bytes = (new File_Content_Request(buffer)).content()
}
